#include "aws_signin_oauth.hpp"

#include "aws_client.hpp"
#include "aws_http_client.hpp"
#include "aws_secret.hpp"

#include "duckdb/common/exception.hpp"
#include "duckdb/common/mutex.hpp"
#include "duckdb/common/printer.hpp"
#include "duckdb/common/unordered_map.hpp"
#include "duckdb/common/string_util.hpp"
#include "duckdb/common/types/blob.hpp"
#include "duckdb/common/types/uuid.hpp"
#include "duckdb/logging/logger.hpp"
#include "duckdb/main/client_context.hpp"
#include "duckdb/main/database.hpp"
#include "duckdb/main/extension/extension_loader.hpp"
#include "duckdb/main/secret/secret.hpp"
#include "duckdb/main/settings.hpp"

#include <aws/core/http/HttpClient.h>
#include <aws/core/http/HttpClientFactory.h>
#include <aws/core/http/HttpRequest.h>
#include <aws/core/http/HttpResponse.h>
#include <aws/core/utils/json/JsonSerializer.h>
#include <aws/core/utils/memory/stl/AWSStringStream.h>

#include <openssl/bn.h>
#include <openssl/core_names.h>
#include <openssl/ecdsa.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/rand.h>

#include <chrono>
#include <thread>

#include "httplib.hpp"

namespace duckdb {

namespace {

//! AWS Sign-In's public OAuth clients, the ones `aws login` uses. The same-device one may only be redirected
//! to http://127.0.0.1:<port>/oauth/callback, which is where the loopback listener below sits; the cross-device
//! one shows the code on a Sign-In page for the user to paste.
constexpr const char *CLIENT_SAME_DEVICE = "arn:aws:signin:::devtools/same-device";
constexpr const char *CLIENT_CROSS_DEVICE = "arn:aws:signin:::devtools/cross-device";
constexpr const char *DEFAULT_OAUTH_SCOPE = "openid";
constexpr int64_t DEFAULT_TIMEOUT_SECONDS = 120;
constexpr const char *CALLBACK_PATH = "/oauth/callback";

//===--------------------------------------------------------------------===//
// Encoding and crypto: PKCE, the DPoP key, ES256
//===--------------------------------------------------------------------===//

string Base64Url(const string &bytes) {
	auto encoded = Blob::ToBase64(bytes);
	string result;
	result.reserve(encoded.size());
	for (auto c : encoded) {
		if (c == '+') {
			result += '-';
		} else if (c == '/') {
			result += '_';
		} else if (c != '=') {
			result += c;
		}
	}
	return result;
}

string RandomBytes(idx_t count) {
	string bytes(count, '\0');
	if (RAND_bytes(reinterpret_cast<unsigned char *>(&bytes[0]), static_cast<int>(count)) != 1) {
		throw InternalException("aws oauth: the random number generator failed");
	}
	return bytes;
}

string Sha256(const string &data) {
	unsigned char digest[EVP_MAX_MD_SIZE];
	unsigned int length = 0;
	if (EVP_Digest(data.data(), data.size(), digest, &length, EVP_sha256(), nullptr) != 1) {
		throw InternalException("aws oauth: SHA-256 failed");
	}
	return string(reinterpret_cast<char *>(digest), length);
}

//! RFC 7636: 43..128 characters of [A-Za-z0-9-._~]; 64 here, each from 256 random bytes mod 66
string PkceVerifier() {
	static const string alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~";
	auto random = RandomBytes(64);
	string verifier;
	for (auto byte : random) {
		verifier += alphabet[static_cast<unsigned char>(byte) % alphabet.size()];
	}
	return verifier;
}

string BigNumToPadded(const BIGNUM *bn, idx_t size) {
	string out(size, '\0');
	if (BN_bn2binpad(bn, reinterpret_cast<unsigned char *>(&out[0]), static_cast<int>(size)) < 0) {
		throw InternalException("aws oauth: BN_bn2binpad failed");
	}
	return out;
}

//! The DPoP key (RFC 9449): an EC P-256 key pair, generated per sign-in and kept with the secret, because the
//! refresh token Sign-In hands back is bound to it. Serialized as PEM so it survives in refresh_info.
class DpopKey {
public:
	static DpopKey Generate() {
		auto *pkey = EVP_PKEY_Q_keygen(nullptr, nullptr, "EC", "P-256");
		if (!pkey) {
			throw InternalException("aws oauth: generating the DPoP key failed");
		}
		return DpopKey(pkey);
	}

	static DpopKey FromPem(const string &pem) {
		auto *bio = BIO_new_mem_buf(pem.data(), static_cast<int>(pem.size()));
		if (!bio) {
			throw InternalException("aws oauth: BIO_new_mem_buf failed");
		}
		auto *pkey = PEM_read_bio_PrivateKey(bio, nullptr, nullptr, nullptr);
		BIO_free(bio);
		if (!pkey) {
			throw InvalidInputException("aws oauth: the stored DPoP key could not be read; sign in again");
		}
		return DpopKey(pkey);
	}

	DpopKey(DpopKey &&other) noexcept : pkey(other.pkey) {
		other.pkey = nullptr;
	}
	DpopKey(const DpopKey &) = delete;
	DpopKey &operator=(const DpopKey &) = delete;
	~DpopKey() {
		if (pkey) {
			EVP_PKEY_free(pkey);
		}
	}

	string ToPem() const {
		auto *bio = BIO_new(BIO_s_mem());
		if (!bio || PEM_write_bio_PrivateKey(bio, pkey, nullptr, nullptr, 0, nullptr, nullptr) != 1) {
			if (bio) {
				BIO_free(bio);
			}
			throw InternalException("aws oauth: writing the DPoP key failed");
		}
		char *data = nullptr;
		auto length = BIO_get_mem_data(bio, &data);
		string pem(data, static_cast<size_t>(length));
		BIO_free(bio);
		return pem;
	}

	//! The public key as a JWK, the member DPoP proofs carry in their header
	string PublicJwk() const {
		BIGNUM *x = nullptr;
		BIGNUM *y = nullptr;
		if (EVP_PKEY_get_bn_param(pkey, OSSL_PKEY_PARAM_EC_PUB_X, &x) != 1 ||
		    EVP_PKEY_get_bn_param(pkey, OSSL_PKEY_PARAM_EC_PUB_Y, &y) != 1) {
			BN_free(x);
			BN_free(y);
			throw InternalException("aws oauth: reading the DPoP public key failed");
		}
		auto jwk = "{\"kty\":\"EC\",\"crv\":\"P-256\",\"x\":\"" + Base64Url(BigNumToPadded(x, 32)) + "\",\"y\":\"" +
		           Base64Url(BigNumToPadded(y, 32)) + "\"}";
		BN_free(x);
		BN_free(y);
		return jwk;
	}

	//! ES256 over `data`: the ECDSA signature as the raw r || s a JWS expects, not DER
	string SignEs256(const string &data) const {
		auto *ctx = EVP_MD_CTX_new();
		if (!ctx) {
			throw InternalException("aws oauth: EVP_MD_CTX_new failed");
		}
		size_t der_length = 0;
		string der;
		bool ok = EVP_DigestSignInit(ctx, nullptr, EVP_sha256(), nullptr, pkey) == 1 &&
		          EVP_DigestSign(ctx, nullptr, &der_length, reinterpret_cast<const unsigned char *>(data.data()),
		                         data.size()) == 1;
		if (ok) {
			der.resize(der_length);
			ok = EVP_DigestSign(ctx, reinterpret_cast<unsigned char *>(&der[0]), &der_length,
			                    reinterpret_cast<const unsigned char *>(data.data()), data.size()) == 1;
			der.resize(der_length);
		}
		EVP_MD_CTX_free(ctx);
		if (!ok) {
			throw InternalException("aws oauth: signing the DPoP proof failed");
		}
		const auto *der_ptr = reinterpret_cast<const unsigned char *>(der.data());
		auto *sig = d2i_ECDSA_SIG(nullptr, &der_ptr, static_cast<long>(der.size()));
		if (!sig) {
			throw InternalException("aws oauth: decoding the ECDSA signature failed");
		}
		auto raw = BigNumToPadded(ECDSA_SIG_get0_r(sig), 32) + BigNumToPadded(ECDSA_SIG_get0_s(sig), 32);
		ECDSA_SIG_free(sig);
		return raw;
	}

private:
	explicit DpopKey(EVP_PKEY *pkey_p) : pkey(pkey_p) {
	}
	EVP_PKEY *pkey;
};

int64_t NowSeconds() {
	return std::chrono::duration_cast<std::chrono::seconds>(std::chrono::system_clock::now().time_since_epoch())
	    .count();
}

int64_t NowMillis() {
	return std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch())
	    .count();
}

//! RFC 9449 proof for one request: a JWS with the public key in its header over {htm, htu, iat, jti}
string DpopProof(const DpopKey &key, const string &method, const string &url) {
	auto header = "{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":" + key.PublicJwk() + "}";
	auto payload = "{\"htm\":\"" + method + "\",\"htu\":\"" + url + "\",\"iat\":" + std::to_string(NowSeconds()) +
	               ",\"jti\":\"" + UUID::ToString(UUID::GenerateRandomUUID()) + "\"}";
	auto input = Base64Url(header) + "." + Base64Url(payload);
	return input + "." + Base64Url(key.SignEs256(input));
}

//===--------------------------------------------------------------------===//
// Sign-In endpoints and the token request
//===--------------------------------------------------------------------===//

struct SigninSettings {
	string region;
	string client_id;
	string oauth_scope = DEFAULT_OAUTH_SCOPE;

	string Base() const {
		return "https://" + region + ".signin.aws.amazon.com";
	}
	string TokenUrl() const {
		return Base() + "/v1/token";
	}
};

//! What Sign-In's error codes mean, in the user's terms
string SigninErrorMessage(const string &code, const string &message) {
	if (code == "AUTHCODE_EXPIRED") {
		return "the authorization code has expired or was already used; sign in again";
	}
	if (code == "INSUFFICIENT_PERMISSIONS") {
		return "this principal may not use AWS Sign-In for developer tools: it needs the SignInLocalDevelopmentAccess "
		       "policy (signin:AuthorizeOAuth2Access and signin:CreateOAuth2Token)";
	}
	if (code == "TOKEN_EXPIRED") {
		return "the console session has ended; sign in again";
	}
	if (code == "USER_CREDENTIALS_CHANGED") {
		return "the password of this principal changed, the session is no longer valid; sign in again";
	}
	return code + (message.empty() ? "" : ": " + message);
}

struct TokenResult {
	string access_key_id;
	string secret_access_key;
	string session_token;
	string refresh_token;
	string id_token;
	int64_t expires_in = 900;
};

//! POST /v1/token with a fresh DPoP proof; `body` is the grant (authorization_code or refresh_token)
TokenResult TokenRequest(ClientContext &context, const SigninSettings &settings, const DpopKey &key,
                         Aws::Utils::Json::JsonValue body) {
	AwsInstanceBinding aws_binding(DatabaseInstance::GetDatabase(context));
	auto url = settings.TokenUrl();
	body.WithString("clientId", settings.client_id.c_str());
	auto payload = body.View().WriteCompact();

	auto client = Aws::Http::CreateHttpClient(BuildClientConfigWithCa());
	auto request = Aws::Http::CreateHttpRequest(Aws::Http::URI(url.c_str()), Aws::Http::HttpMethod::HTTP_POST,
	                                            Aws::Utils::Stream::DefaultResponseStreamFactoryMethod);
	request->SetHeaderValue("content-type", "application/json");
	request->SetHeaderValue("dpop", DpopProof(key, "POST", url).c_str());
	auto stream = Aws::MakeShared<Aws::StringStream>("aws-oauth");
	*stream << payload;
	request->AddContentBody(stream);
	request->SetContentLength(std::to_string(payload.size()).c_str());
	auto response = client->MakeRequest(request);
	if (!response) {
		throw IOException("aws oauth: no response from %s", url);
	}
	std::stringstream response_body;
	response_body << response->GetResponseBody().rdbuf();
	auto text = response_body.str();
	auto status = static_cast<int>(response->GetResponseCode());

	Aws::Utils::Json::JsonValue json(text.c_str());
	if (status < 200 || status >= 300) {
		string code, message;
		if (json.WasParseSuccessful()) {
			auto view = json.View();
			if (view.ValueExists("error")) {
				code = view.GetString("error").c_str();
			}
			if (view.ValueExists("message")) {
				message = view.GetString("message").c_str();
			}
		}
		if (code.empty()) {
			throw IOException("aws oauth: AWS Sign-In answered HTTP %d: %s", status, text.substr(0, 300));
		}
		throw IOException("aws oauth: AWS Sign-In: %s", SigninErrorMessage(code, message));
	}
	if (!json.WasParseSuccessful()) {
		throw IOException("aws oauth: AWS Sign-In answered with something that is not JSON");
	}
	auto view = json.View();
	auto out = view.ValueExists("tokenOutput") ? view.GetObject("tokenOutput") : view;
	TokenResult result;
	if (!out.ValueExists("accessToken") || !out.GetObject("accessToken").ValueExists("accessKeyId")) {
		throw IOException("aws oauth: AWS Sign-In's answer holds no credentials");
	}
	auto token = out.GetObject("accessToken");
	result.access_key_id = token.GetString("accessKeyId").c_str();
	result.secret_access_key = token.GetString("secretAccessKey").c_str();
	result.session_token = token.GetString("sessionToken").c_str();
	if (out.ValueExists("refreshToken")) {
		result.refresh_token = out.GetString("refreshToken").c_str();
	}
	if (out.ValueExists("idToken")) {
		result.id_token = out.GetString("idToken").c_str();
	}
	if (out.ValueExists("expiresIn")) {
		result.expires_in = out.GetInt64("expiresIn");
	}
	return result;
}

//! The `sub` of the ID token, the ARN of the signed-in principal; "" when it cannot be read
string IdentityOf(const string &id_token) {
	auto parts = StringUtil::Split(id_token, '.');
	if (parts.size() < 2) {
		return string();
	}
	auto payload = parts[1];
	for (auto &c : payload) {
		if (c == '-') {
			c = '+';
		} else if (c == '_') {
			c = '/';
		}
	}
	while (payload.size() % 4 != 0) {
		payload += '=';
	}
	try {
		Aws::Utils::Json::JsonValue json(Blob::FromBase64(payload).c_str());
		if (json.WasParseSuccessful() && json.View().ValueExists("sub")) {
			return json.View().GetString("sub").c_str();
		}
	} catch (std::exception &) {
	}
	return string();
}

//===--------------------------------------------------------------------===//
// The authorization leg: browser and loopback callback, or a pasted code
//===--------------------------------------------------------------------===//

string UrlEncode(const string &value) {
	static const char *hex = "0123456789ABCDEF";
	string out;
	for (unsigned char c : value) {
		if (isalnum(c) || c == '-' || c == '_' || c == '.' || c == '~') {
			out += static_cast<char>(c);
		} else {
			out += '%';
			out += hex[c >> 4];
			out += hex[c & 15];
		}
	}
	return out;
}

string AuthorizeUrl(const SigninSettings &settings, const string &challenge, const string &state,
                    const string &redirect_uri) {
	return settings.Base() + "/v1/authorize?response_type=code&client_id=" + UrlEncode(settings.client_id) +
	       "&state=" + UrlEncode(state) + "&code_challenge_method=SHA-256&code_challenge=" + challenge +
	       "&scope=" + UrlEncode(settings.oauth_scope) + "&redirect_uri=" + UrlEncode(redirect_uri);
}

//! Best effort: the URL is also returned to the user in every message, so a failure here is not an error
bool OpenBrowser(const string &url) {
	string quoted;
	for (auto c : url) {
		if (c == '\'') {
			quoted += "'\\''";
		} else {
			quoted += c;
		}
	}
#if defined(__APPLE__)
	auto command = "open '" + quoted + "' >/dev/null 2>&1";
#elif defined(_WIN32)
	auto command = "start \"\" \"" + url + "\"";
#else
	auto command = "xdg-open '" + quoted + "' >/dev/null 2>&1";
#endif
	return std::system(command.c_str()) == 0;
}

//! A sign-in started with MODE 'code', waiting for its code to come back through CODE: the verifier and the
//! DPoP key never leave the process, so a pasted code can only be redeemed by the session that started it.
struct PendingSignin {
	string verifier;
	string key_pem;
	SigninSettings settings;
	string redirect_uri;
};

mutex pending_lock;
unordered_map<string, PendingSignin> pending_signins; // by state

//! Listens on 127.0.0.1 for the one redirect Sign-In makes to the same-device client, then stops. Only
//! /oauth/callback is served, only the first answer counts, and the code is useless without the verifier
//! held by the caller; everything else is refused.
struct CallbackResult {
	string code;
	string state;
	string error;
	string error_description;
	bool received = false;
};

CallbackResult WaitForCallback(ClientContext &context, duckdb_httplib::Server &server, std::thread &listener,
                               int64_t timeout_seconds, CallbackResult &result, mutex &result_lock) {
	auto deadline = std::chrono::steady_clock::now() + std::chrono::seconds(timeout_seconds);
	bool timed_out = false;
	while (true) {
		{
			lock_guard<mutex> guard(result_lock);
			if (result.received) {
				break;
			}
		}
		if (std::chrono::steady_clock::now() >= deadline) {
			timed_out = true;
			break;
		}
		context.InterruptCheck();
		std::this_thread::sleep_for(std::chrono::milliseconds(50));
	}
	server.stop();
	listener.join();
	if (timed_out) {
		throw IOException("aws oauth: no sign-in within %lld seconds; open the URL that was printed, or use MODE "
		                  "'code' and TIMEOUT_SECONDS",
		                  static_cast<long long>(timeout_seconds));
	}
	return result;
}

//! Opens the browser on Sign-In and receives the code on a loopback port: the whole same-device flow
CallbackResult BrowserSignin(ClientContext &context, const SigninSettings &settings, const string &challenge,
                             const string &state, int64_t timeout_seconds, string &redirect_uri_out) {
	duckdb_httplib::Server server;
	CallbackResult result;
	mutex result_lock;
	server.Get(CALLBACK_PATH, [&](const duckdb_httplib::Request &req, duckdb_httplib::Response &res) {
		lock_guard<mutex> guard(result_lock);
		if (result.received) {
			res.status = 409;
			res.set_content("This sign-in was already completed.", "text/plain");
			return;
		}
		result.received = true;
		result.code = req.get_param_value("code");
		result.state = req.get_param_value("state");
		result.error = req.get_param_value("error");
		result.error_description = req.get_param_value("error_description");
		res.set_content(result.error.empty() ? "Signed in to AWS. You can close this tab and return to DuckDB."
		                                     : "AWS Sign-In reported: " + result.error + ". Return to DuckDB.",
		                "text/plain");
	});
	auto port = server.bind_to_any_port("127.0.0.1");
	if (port <= 0) {
		throw IOException("aws oauth: could not listen on 127.0.0.1 for the sign-in callback");
	}
	redirect_uri_out = "http://127.0.0.1:" + std::to_string(port) + CALLBACK_PATH;
	std::thread listener([&server] { server.listen_after_bind(); });

	auto url = AuthorizeUrl(settings, challenge, state, redirect_uri_out);
	auto opened = OpenBrowser(url);
	DUCKDB_LOG_INFO(context, "aws.oauth: %s %s", opened ? "opened the browser on" : "open this URL to sign in:", url);
	if (!opened) {
		// the message is the only channel to the user here; the statement keeps waiting on the listener
		Printer::Print("Open this URL in a browser to sign in to AWS:\n" + url);
	}
	return WaitForCallback(context, server, listener, timeout_seconds, result, result_lock);
}

//===--------------------------------------------------------------------===//
// The secret
//===--------------------------------------------------------------------===//

vector<string> DefaultScope(const Identifier &type) {
	if (type == Identifier("s3")) {
		return {"s3://", "s3n://", "s3a://"};
	}
	return {""};
}

int64_t Int64Option(CreateSecretInput &input, const string &name, int64_t default_value) {
	auto entry = input.options.find(name);
	if (entry == input.options.end() || entry->second.IsNull()) {
		return default_value;
	}
	return entry->second.GetValue<int64_t>();
}

unique_ptr<BaseSecret> BuildSecret(CreateSecretInput &input, const SigninSettings &settings, const DpopKey &key,
                                   const TokenResult &tokens, bool refresh) {
	auto scope = input.scope.empty() ? DefaultScope(input.type) : input.scope;
	auto secret = make_uniq<KeyValueSecret>(scope, input.type, input.provider, input.name);
	secret->redact_keys = {"secret", "session_token", "refresh_info"};
	secret->secret_map["key_id"] = Value(tokens.access_key_id);
	secret->secret_map["secret"] = Value(tokens.secret_access_key);
	secret->secret_map["session_token"] = Value(tokens.session_token);
	secret->secret_map["region"] = Value(settings.region);
	secret->secret_map["expiration_epoch_ms"] = Value::BIGINT(NowMillis() + tokens.expires_in * 1000);
	auto identity = IdentityOf(tokens.id_token);
	if (!identity.empty()) {
		secret->secret_map["identity"] = Value(identity);
	}
	// what a refresh needs: the provider is re-run with these as its options (see httpfs refresh_info). On by
	// default: the credentials last 15 minutes, the refresh token the rest of the console session.
	if (refresh && !tokens.refresh_token.empty()) {
		child_list_t<Value> refresh;
		refresh.emplace_back("region", Value(settings.region));
		refresh.emplace_back("client", Value(settings.client_id));
		refresh.emplace_back("oauth_scope", Value(settings.oauth_scope));
		refresh.emplace_back("refresh_token", Value(tokens.refresh_token));
		refresh.emplace_back("dpop_key", Value(key.ToPem()));
		secret->secret_map["refresh_info"] = Value::STRUCT(std::move(refresh));
	}
	return std::move(secret);
}

unique_ptr<BaseSecret> CreateAWSSecretFromOAuth(ClientContext &context, CreateSecretInput &input) {
	if (!Settings::Get<EnableExternalAccessSetting>(context)) {
		throw PermissionException("The oauth provider cannot be used when external access is disabled "
		                          "(enable_external_access)");
	}
	SigninSettings settings;
	settings.region = TryGetStringParam(input, "region");
	settings.client_id = TryGetStringParam(input, "client");
	auto oauth_scope = TryGetStringParam(input, "oauth_scope");
	if (!oauth_scope.empty()) {
		settings.oauth_scope = oauth_scope;
	}
	auto refresh_token = TryGetStringParam(input, "refresh_token");
	auto code = TryGetStringParam(input, "code");
	auto mode = StringUtil::Lower(TryGetStringParam(input, "mode"));
	auto timeout_seconds = Int64Option(input, "timeout_seconds", DEFAULT_TIMEOUT_SECONDS);
	auto refresh_option = StringUtil::Lower(TryGetStringParam(input, "refresh"));
	if (!refresh_option.empty() && refresh_option != "auto" && refresh_option != "none") {
		throw InvalidInputException("oauth provider: REFRESH must be 'auto' (default) or 'none'");
	}
	bool refresh = refresh_option != "none";
	if (settings.region.empty()) {
		throw InvalidInputException("oauth provider: REGION is required, the region of the AWS Sign-In endpoint "
		                            "(e.g. REGION 'us-east-1')");
	}

	// 1. a refresh: the secret re-creating itself from its refresh token
	if (!refresh_token.empty()) {
		auto key = DpopKey::FromPem(TryGetStringParam(input, "dpop_key"));
		Aws::Utils::Json::JsonValue body;
		body.WithString("grantType", "refresh_token").WithString("refreshToken", refresh_token.c_str());
		auto tokens = TokenRequest(context, settings, key, std::move(body));
		if (tokens.refresh_token.empty()) {
			tokens.refresh_token = refresh_token;
		}
		return BuildSecret(input, settings, key, tokens, refresh);
	}

	// 2. a pasted code completing a sign-in started with MODE 'code'
	if (!code.empty()) {
		string decoded;
		try {
			decoded = Blob::FromBase64(StringUtil::Replace(code, " ", ""));
		} catch (std::exception &) {
			throw InvalidInputException("oauth provider: CODE is not the code AWS Sign-In showed");
		}
		string code_value, state;
		for (auto &pair : StringUtil::Split(decoded, '&')) {
			auto eq = pair.find('=');
			if (eq == string::npos) {
				continue;
			}
			auto key_name = pair.substr(0, eq);
			if (key_name == "code") {
				code_value = pair.substr(eq + 1);
			} else if (key_name == "state") {
				state = pair.substr(eq + 1);
			}
		}
		if (code_value.empty() || state.empty()) {
			throw InvalidInputException("oauth provider: CODE is missing its state or authorization code");
		}
		PendingSignin pending;
		{
			lock_guard<mutex> guard(pending_lock);
			auto entry = pending_signins.find(state);
			if (entry == pending_signins.end()) {
				throw InvalidInputException("oauth provider: this code belongs to no sign-in started in this process "
				                            "with MODE 'code'; start one and paste the code it shows");
			}
			pending = std::move(entry->second);
			pending_signins.erase(entry);
		}
		auto key = DpopKey::FromPem(pending.key_pem);
		Aws::Utils::Json::JsonValue body;
		body.WithString("grantType", "authorization_code")
		    .WithString("code", code_value.c_str())
		    .WithString("codeVerifier", pending.verifier.c_str())
		    .WithString("redirectUri", pending.redirect_uri.c_str());
		auto tokens = TokenRequest(context, pending.settings, key, std::move(body));
		return BuildSecret(input, pending.settings, key, tokens, refresh);
	}

	// 3. a new sign-in
	if (!mode.empty() && mode != "browser" && mode != "code") {
		throw InvalidInputException("oauth provider: MODE must be 'browser' (default) or 'code'");
	}
	auto verifier = PkceVerifier();
	auto challenge = Base64Url(Sha256(verifier));
	auto state = UUID::ToString(UUID::GenerateRandomUUID());
	auto key = DpopKey::Generate();

	if (mode == "code") {
		if (settings.client_id.empty()) {
			settings.client_id = CLIENT_CROSS_DEVICE;
		}
		PendingSignin pending;
		pending.verifier = verifier;
		pending.key_pem = key.ToPem();
		pending.settings = settings;
		pending.redirect_uri = settings.Base() + "/v1/sessions/confirmation";
		auto url = AuthorizeUrl(settings, challenge, state, pending.redirect_uri);
		{
			lock_guard<mutex> guard(pending_lock);
			pending_signins[state] = std::move(pending);
		}
		throw InvalidInputException("oauth provider: sign in at\n  %s\nthen run the same CREATE SECRET with CODE "
		                            "'<the code AWS Sign-In shows>'",
		                            url);
	}

	if (settings.client_id.empty()) {
		settings.client_id = CLIENT_SAME_DEVICE;
	}
	string redirect_uri;
	auto callback = BrowserSignin(context, settings, challenge, state, timeout_seconds, redirect_uri);
	if (!callback.error.empty()) {
		throw IOException("aws oauth: AWS Sign-In: %s", SigninErrorMessage(callback.error, callback.error_description));
	}
	if (callback.state != state) {
		throw IOException("aws oauth: the sign-in that came back is not the one this statement started");
	}
	Aws::Utils::Json::JsonValue body;
	body.WithString("grantType", "authorization_code")
	    .WithString("code", callback.code.c_str())
	    .WithString("codeVerifier", verifier.c_str())
	    .WithString("redirectUri", redirect_uri.c_str());
	auto tokens = TokenRequest(context, settings, key, std::move(body));
	return BuildSecret(input, settings, key, tokens, refresh);
}

} // namespace

void AwsSigninOAuth::Register(ExtensionLoader &loader) {
	for (const auto &type : {"aws", "s3"}) {
		CreateSecretFunction function = {type, "oauth", CreateAWSSecretFromOAuth};
		function.named_parameters["region"] = LogicalType::VARCHAR;
		function.named_parameters["mode"] = LogicalType::VARCHAR;
		function.named_parameters["code"] = LogicalType::VARCHAR;
		function.named_parameters["timeout_seconds"] = LogicalType::BIGINT;
		function.named_parameters["oauth_scope"] = LogicalType::VARCHAR;
		function.named_parameters["client"] = LogicalType::VARCHAR;
		function.named_parameters["refresh"] = LogicalType::VARCHAR;
		// set by a refresh only: the fields of refresh_info come back as options
		function.named_parameters["refresh_token"] = LogicalType::VARCHAR;
		function.named_parameters["dpop_key"] = LogicalType::VARCHAR;
		loader.RegisterFunction(function);
	}
}

} // namespace duckdb

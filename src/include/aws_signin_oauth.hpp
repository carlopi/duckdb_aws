#pragma once

#include "duckdb.hpp"

namespace duckdb {
class ExtensionLoader;

//! The `oauth` secret provider: signs in to AWS through AWS Sign-In's OAuth 2.0 flow (authorization code
//! with PKCE, DPoP-bound tokens), the flow of `aws login`, and holds the SigV4 credentials it hands back,
//! refreshed from the refresh token until the console session ends.
struct AwsSigninOAuth {
	static void Register(ExtensionLoader &loader);
};

} // namespace duckdb

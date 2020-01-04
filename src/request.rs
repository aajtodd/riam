use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Authorization request context. Consists of key/value pairs that the caller is expected to
/// gather and send with a request to enable condition evaluation. A policy that has conditions
/// will fail if the context is missing.
#[derive(Serialize, Deserialize, Default, PartialEq, Debug)]
pub struct Context(pub HashMap<String, String>);

impl Context {
    /// Returns `true` if the context contains no values.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// AuthRequest represents an attempted action on a resource. It describes who, what, and how
/// the resource in question is to be accessed and is used to make authorization decisions.
#[derive(Serialize, Deserialize, PartialEq, Debug)]
pub struct AuthRequest {
    /// The subject (user/group/etc) attempting the action
    pub principal: String,

    /// The name of the action being taken
    pub action: String,

    /// The resources being acted upon
    pub resource: String,

    /// The request context
    #[serde(
        skip_serializing_if = "Context::is_empty",
        default = "Context::default"
    )]
    pub context: Context,
}

impl AuthRequest {
    /// Create a new authorization request
    ///
    /// # Example
    /// ```
    /// # use riam::AuthRequest;
    /// let req = AuthRequest::new("users:john", "actions:list-accounts", "resources:account:123");
    /// ```
    pub fn new(principal: &str, action: &str, resource: &str) -> Self {
        AuthRequest {
            principal: principal.to_owned(),
            action: action.to_owned(),
            resource: resource.to_owned(),
            context: Context::default(),
        }
    }

    /// Insert additional context into the authorization request
    ///
    /// # Example
    /// ```
    /// # use riam::AuthRequest;
    /// let mut req = AuthRequest::new("users:john", "actions:list-accounts", "resources:account:123");
    /// req.with_context("k1", "v1")
    ///    .with_context("k2", "v2");
    /// assert_eq!(req.context.0.get("k1"), Some(&"v1".to_owned()));
    /// ```
    pub fn with_context<'a, T>(&'a mut self, key: T, value: T) -> &'a mut Self
    where
        T: Into<String>,
    {
        // let ctx = self.context.get_or_insert_with(Context::default);
        self.context.0.insert(key.into(), value.into());
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_test::{assert_tokens, Token};

    #[test]
    fn test_auth_request_serialization() {
        let mut ctx_map = HashMap::new();
        ctx_map.insert("k1".to_owned(), "v1".to_owned());
        let req = AuthRequest {
            principal: "users:test-user".into(),
            action: "actions:list-accounts".into(),
            resource: "resources:accounts:123".into(),
            context: Context(ctx_map),
        };

        assert_tokens(
            &req,
            &[
                Token::Struct {
                    name: "AuthRequest",
                    len: 4,
                },
                Token::Str("principal"),
                Token::Str("users:test-user"),
                Token::Str("action"),
                Token::Str("actions:list-accounts"),
                Token::Str("resource"),
                Token::Str("resources:accounts:123"),
                Token::Str("context"),
                Token::NewtypeStruct { name: "Context" },
                Token::Map { len: Some(1) },
                Token::Str("k1"),
                Token::Str("v1"),
                Token::MapEnd,
                Token::StructEnd,
            ],
        );
    }
}

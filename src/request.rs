use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::HashMap;

/// Authorization request context. Consists of key/value pairs that the caller is expected to
/// gather and send with a request to enable condition evaluation.
///
/// A policy that has conditions (with the exception of `IfExists` conditions) will fail if the context is missing.
/// A condition will also fail if the context value does not match the expected values for the condition.
/// e.g. A `StringEquals` condition only accepts a scalar string value or a sequence
/// of strings (`"v1"` or `["v1", "v2"]`). It does not accept numeric, null, map values, etc.
///
#[derive(Serialize, Deserialize, Default, PartialEq, Debug)]
pub struct Context(HashMap<String, Value>);

impl Context {
    /// Create a new request context conditions will be evaluated against.
    pub fn new() -> Self {
        Context::default()
    }

    /// Insert a key value pair into the context under the given key.
    /// Unlike Rust standard Map types, values are replaced not updated.
    ///
    /// # Example
    /// ```
    /// # use riam::Context;
    /// let mut context = Context::new();
    /// context.insert("str", "mystring")
    ///        .insert("int", 2)
    ///        .insert("float", 3.4)
    ///        .insert("array", vec!["v1", "v2", "v3"]);
    ///
    /// // Resulting context:
    /// // {
    /// //     "str": "mystring",
    /// //     "int": 2,
    /// //     "float": 3.4,
    /// //     "array": ["v1", "v2", "v3"]
    /// // }
    /// ```
    ///
    pub fn insert<K, V>(&mut self, k: K, v: V) -> &mut Self
    where
        K: Into<String>,
        V: Into<Value>,
    {
        self.0.insert(k.into(), v.into());
        self
    }

    /// Returns `true` if the context contains no values.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// An iterator visiting all key-value pairs in arbitrary order. The iterator element type is (&'a String, &'a Value).
    pub fn iter(&self) -> ::std::collections::hash_map::Iter<String, Value> {
        self.0.iter()
    }

    /// Returns a reference to the value corresponding to the key.
    pub fn get(&self, k: &str) -> Option<&Value> {
        self.0.get(k)
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
    #[serde(skip_serializing_if = "Context::is_empty", default = "Context::default")]
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
    /// # use serde_json::Value;
    /// let mut req = AuthRequest::new("users:john", "actions:list-accounts", "resources:account:123");
    /// req.with_context("k1", "v1")
    ///    .with_context("k2", "v2");
    /// assert_eq!(req.context.get("k1"), Some(&Value::String("v1".into())));
    /// ```
    pub fn with_context<K, T>(&mut self, key: K, value: T) -> &mut Self
    where
        K: Into<String>,
        T: Into<Value>,
    {
        self.context.insert(key.into(), value.into());
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_test::{assert_tokens, Token};

    #[test]
    fn test_auth_request_serialization() {
        let mut ctx = Context::new();
        ctx.insert("k1", "v1");
        let req = AuthRequest {
            principal: "users:test-user".into(),
            action: "actions:list-accounts".into(),
            resource: "resources:accounts:123".into(),
            context: ctx,
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

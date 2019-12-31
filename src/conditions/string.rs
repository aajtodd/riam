use super::condition::{self, Body, ScalarOrSeq};
use super::Eval;
use crate::Context;
use serde::{Deserialize, Serialize};

/// Exact matching, case sensitive
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct StringEquals(condition::Body<String>);

impl StringEquals {
    /// Create a new condition with initial key/value pair
    pub fn new<S>(key: S, value: S) -> Self
    where
        S: Into<String>,
    {
        StringEquals(Body::new(key.into(), value.into()))
    }

    /// Add additional key/value pairs. If the key already exists the
    /// value is appended to the list of allowed values for this key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use riam::conditions::StringEquals;
    /// let cond = StringEquals::new("k1", "v1").add("k1", "v2");
    /// // Equivalent to JSON condition:
    /// // {"StringEquals": {"k1": ["v1","v2"]}}
    /// ```
    pub fn add<S>(mut self, key: S, value: S) -> Self
    where
        S: Into<String>,
    {
        self.0.insert(key.into(), value.into());
        self
    }
}

impl Eval for StringEquals {
    fn evaluate(&self, ctx: &Context) -> bool {
        for (key, values) in (self.0).0.iter() {
            // all keys are and'd together to pass the condition
            let valid = ctx
                .0
                .get(key)
                // possible value's are OR'd together for evaluation (only 1 needs to pass)
                .and_then(|x| match values {
                    ScalarOrSeq::Scalar(sc) => Some(x == sc),
                    ScalarOrSeq::Seq(seq) => Some(seq.contains(x)),
                })
                .unwrap_or(false);

            if !valid {
                return false;
            }
        }
        true
    }
}

/// Negated Matching
#[derive(Serialize, Deserialize, PartialEq, Debug)]
pub struct StringNotEquals(condition::Body<String>);

impl StringNotEquals {
    /// Create a new condition with initial key/value pair
    pub fn new<S>(key: S, value: S) -> Self
    where
        S: Into<String>,
    {
        StringNotEquals(Body::new(key.into(), value.into()))
    }

    /// Add additional key/value pairs. If the key already exists the
    /// value is appended to the list of allowed values for this key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use riam::conditions::StringEquals;
    /// let cond = StringEquals::new("k1", "v1").add("k1", "v2");
    /// // Equivalent to JSON condition:
    /// // {"StringNotEquals": {"k1": ["v1","v2"]}}
    /// ```
    pub fn add<S>(mut self, key: S, value: S) -> Self
    where
        S: Into<String>,
    {
        self.0.insert(key.into(), value.into());
        self
    }
}

impl Eval for StringNotEquals {
    fn evaluate(&self, ctx: &Context) -> bool {
        for (key, values) in (self.0).0.iter() {
            let valid = ctx
                .0
                .get(key)
                .and_then(|x| match values {
                    ScalarOrSeq::Scalar(sc) => Some(x != sc),
                    ScalarOrSeq::Seq(seq) => Some(!seq.contains(x)),
                })
                .unwrap_or(false);

            if !valid {
                return false;
            }
        }
        true
    }
}

// TODO - need to implement the rest of the string types
//     - perhaps a macro for shared component functionality (new/add)

/// Exact matching, ignoring (value) case.
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct StringEqualsIgnoreCase(condition::Body<String>);

/// Negated matching, ignoring (value) case.
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct StringNotEqualsIgnoreCase(condition::Body<String>);

/// Case-sensitive matching. The values can include a multi-character match wildcard (*) or a single-character match wildcard (?) anywhere in the string.
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct StringLike(condition::Body<String>);

/// Negated case-sensitive matching. The values can include a multi-character match wildcard (*) or a single-character match wildcard (?) anywhere in the string.
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct StringNotLike(condition::Body<String>);

#[cfg(test)]
mod tests {
    use super::super::*;
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_string_equals_json() {
        let jsp = r#"
        {
            "StringEquals": {
                "mykey": "myvalue"
            }
        }
        "#;

        let actual: Condition = serde_json::from_str(jsp).unwrap();
        let expected = Condition::StringEquals(StringEquals(Body::new(
            "mykey".to_owned(),
            "myvalue".to_owned(),
        )));
        assert_eq!(expected, actual);

        let serialized = serde_json::to_string(&expected).unwrap();
        let expected = r#"{"StringEquals":{"mykey":"myvalue"}}"#;
        assert_eq!(expected, serialized);
    }

    #[test]
    fn test_string_not_equals_json() {
        let jsp = r#"
        {
            "StringNotEquals": {
                "mykey": "myvalue"
            }
        }
        "#;

        let actual: Condition = serde_json::from_str(jsp).unwrap();
        let expected = Condition::StringNotEquals(StringNotEquals::new("mykey", "myvalue"));
        assert_eq!(expected, actual);

        let serialized = serde_json::to_string(&expected).unwrap();
        let expected = r#"{"StringNotEquals":{"mykey":"myvalue"}}"#;
        assert_eq!(expected, serialized);
    }

    #[test]
    fn test_eval_string_equals() {
        // singular
        let cond = StringEquals::new("k1", "v1");

        let mut ctx = Context(HashMap::new());
        ctx.0.insert("k1".into(), "v1".into());

        assert!(cond.evaluate(&ctx));

        ctx.0.insert("k1".to_owned(), "v2".to_owned());
        assert!(!cond.evaluate(&ctx));

        // multiple allowed
        let cond = StringEquals::new("k1", "v1").add("k1", "v2");
        assert!(cond.evaluate(&ctx));

        ctx.0.insert("k1".to_owned(), "v3".to_owned());
        assert!(!cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_string_not_equals() {
        // singular
        let cond = StringNotEquals::new("k1", "v1");
        let mut ctx = Context(HashMap::new());
        ctx.0.insert("k1".into(), "v2".into());
        assert!(cond.evaluate(&ctx));

        ctx.0.insert("k1".to_owned(), "v1".to_owned());
        assert!(!cond.evaluate(&ctx));

        // multiple not allowed
        let cond = StringNotEquals::new("k1", "v1").add("k1", "v2");
        assert!(!cond.evaluate(&ctx));

        ctx.0.insert("k1".to_owned(), "v3".to_owned());
        assert!(cond.evaluate(&ctx));
    }
}
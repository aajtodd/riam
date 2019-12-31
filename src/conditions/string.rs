use super::condition::{self, Body, ScalarOrSeq};
use super::Eval;
use crate::wildcard;
use crate::Context;
use serde::{Deserialize, Serialize};

macro_rules! impl_str_cond {
    ($x:ident, $sname:expr) => {
        impl $x {
            /// Create a new condition with initial key/value pair
            pub fn new<S>(key: S, value: S) -> Self
            where
                S: Into<String>,
            {
                $x(Body::new(key.into(), value.into()))
            }

            // FIXME - the generated documentation (and doctest) will use the same example/type
            // regardless of the type passed to the macro
            /// Add additional key/value pairs. If the key already exists the
            /// value is appended to the list of allowed values for this key.
            ///
            /// # Example
            /// NOTE: The example uses `StringEquals` however the method works the same for
            /// all String* condition operators.
            ///
            /// ```
            /// # use riam::conditions::StringEquals;
            /// let cond = StringEquals::new("k1", "v1").add("k1", "v2");
            /// // equivalent JSON:
            /// // {"StringEquals":{"k1": ["v1", "v2"]}}
            /// ```
            pub fn add<S>(mut self, key: S, value: S) -> Self
            where
                S: Into<String>,
            {
                self.0.insert(key.into(), value.into());
                self
            }
        }
    };

    ($name:tt) => {
        impl_str_cond!($name, stringify!($name));
    };
}

/// Exact matching, case sensitive
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct StringEquals(condition::Body<String>);

impl_str_cond!(StringEquals);

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

impl_str_cond!(StringNotEquals);

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

/// Exact matching, ignoring (value) case.
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct StringEqualsIgnoreCase(condition::Body<String>);

impl_str_cond!(StringEqualsIgnoreCase);

impl Eval for StringEqualsIgnoreCase {
    fn evaluate(&self, ctx: &Context) -> bool {
        for (key, values) in (self.0).0.iter() {
            let valid = ctx
                .0
                .get(key)
                .and_then(|x| Some(x.to_lowercase()))
                .and_then(|x| match values {
                    ScalarOrSeq::Scalar(sc) => Some(x.to_lowercase() == sc.to_lowercase()),
                    ScalarOrSeq::Seq(seq) => {
                        Some(seq.iter().map(|v| v.to_lowercase()).any(|v| v == x))
                    }
                })
                .unwrap_or(false);

            if !valid {
                return false;
            }
        }
        true
    }
}

/// Negated matching, ignoring (value) case.
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct StringNotEqualsIgnoreCase(condition::Body<String>);

impl_str_cond!(StringNotEqualsIgnoreCase);

impl Eval for StringNotEqualsIgnoreCase {
    fn evaluate(&self, ctx: &Context) -> bool {
        for (key, values) in (self.0).0.iter() {
            let valid = ctx
                .0
                .get(key)
                .and_then(|x| Some(x.to_lowercase()))
                .and_then(|x| match values {
                    ScalarOrSeq::Scalar(sc) => Some(x.to_lowercase() != sc.to_lowercase()),
                    ScalarOrSeq::Seq(seq) => {
                        Some(seq.iter().map(|v| v.to_lowercase()).all(|v| v != x))
                    }
                })
                .unwrap_or(false);

            if !valid {
                return false;
            }
        }
        true
    }
}

/// Case-sensitive matching. The values can include a multi-character match wildcard (*) anywhere in the string.
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct StringLike(condition::Body<String>);

impl_str_cond!(StringLike);

impl Eval for StringLike {
    fn evaluate(&self, ctx: &Context) -> bool {
        for (key, values) in (self.0).0.iter() {
            let valid = ctx
                .0
                .get(key)
                .and_then(|x| match values {
                    ScalarOrSeq::Scalar(sc) => Some(wildcard::matches(sc, x)),
                    ScalarOrSeq::Seq(seq) => Some(seq.iter().any(|p| wildcard::matches(p, x))),
                })
                .unwrap_or(false);

            if !valid {
                return false;
            }
        }
        true
    }
}

/// Negated case-sensitive matching. The values can include a multi-character match wildcard (*) anywhere in the string.
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct StringNotLike(condition::Body<String>);

impl_str_cond!(StringNotLike);

impl Eval for StringNotLike {
    fn evaluate(&self, ctx: &Context) -> bool {
        for (key, values) in (self.0).0.iter() {
            let valid = ctx
                .0
                .get(key)
                .and_then(|x| match values {
                    ScalarOrSeq::Scalar(sc) => Some(!wildcard::matches(sc, x)),
                    ScalarOrSeq::Seq(seq) => Some(seq.iter().all(|p| !wildcard::matches(p, x))),
                })
                .unwrap_or(false);

            if !valid {
                return false;
            }
        }
        true
    }
}

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

    #[test]
    fn test_eval_string_equals_ignore_case() {
        // singular
        let cond = StringEqualsIgnoreCase::new("k1", "value1");

        let mut ctx = Context(HashMap::new());
        ctx.0.insert("k1".into(), "VaLue1".into());

        assert!(cond.evaluate(&ctx));

        ctx.0.insert("k1".to_owned(), "value2".to_owned());
        assert!(!cond.evaluate(&ctx));

        // multiple allowed
        let cond = StringEqualsIgnoreCase::new("k1", "VaLue1").add("k1", "ValUE2");
        assert!(cond.evaluate(&ctx));

        ctx.0.insert("k1".to_owned(), "v3".to_owned());
        assert!(!cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_string_not_equals_ignore_case() {
        // singular
        let cond = StringNotEqualsIgnoreCase::new("k1", "value1");

        let mut ctx = Context(HashMap::new());
        ctx.0.insert("k1".into(), "VaLue2".into());

        assert!(cond.evaluate(&ctx));

        ctx.0.insert("k1".to_owned(), "VaLue1".to_owned());
        assert!(!cond.evaluate(&ctx));

        // multiple not allowed
        let cond = StringNotEqualsIgnoreCase::new("k1", "VaLue1").add("k1", "ValUE2");
        assert!(!cond.evaluate(&ctx));

        ctx.0.insert("k1".to_owned(), "VaLue3".to_owned());
        assert!(cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_string_like() {
        // singular
        let cond = StringLike::new("k1", "re*123");

        let mut ctx = Context(HashMap::new());
        ctx.0.insert("k1".into(), "resources:blog:123".into());

        assert!(cond.evaluate(&ctx));

        ctx.0
            .insert("k1".to_owned(), "resources:blog:456".to_owned());
        assert!(!cond.evaluate(&ctx));

        // multiple allowed
        let cond = StringLike::new("k1", "resources:*:123").add("k1", "resources:*:456");
        assert!(cond.evaluate(&ctx));

        ctx.0
            .insert("k1".to_owned(), "resources:blog:789".to_owned());
        assert!(!cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_string_not_like() {
        // singular
        let cond = StringNotLike::new("k1", "re*123");

        let mut ctx = Context(HashMap::new());
        ctx.0.insert("k1".into(), "resources:blog:123".into());

        assert!(!cond.evaluate(&ctx));

        ctx.0.insert("k1".into(), "resources:blog:456".into());
        assert!(cond.evaluate(&ctx));

        // multiple not allowed
        let cond = StringNotLike::new("k1", "resources:*:123").add("k1", "resources:*:456");
        assert!(!cond.evaluate(&ctx));

        ctx.0
            .insert("k1".to_owned(), "resources:blog:789".to_owned());
        assert!(cond.evaluate(&ctx));
    }
}

use crate::Context;
use enum_dispatch::enum_dispatch;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use super::string::{
    StringEquals, StringEqualsIgnoreCase, StringLike, StringNotEquals, StringNotEqualsIgnoreCase,
    StringNotLike,
};

// Scalar (singular) or sequence (multiple) of values.
//
// Type `ScalarOrSeq` holds either a single value or a vector of values.
// Used internally to serialize/deserialize either JSON type easily (via untagged).
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
#[serde(untagged)]
pub(in crate::conditions) enum ScalarOrSeq<T> {
    Scalar(T),
    Seq(Vec<T>),
}

// Condition Body
//
// Condition bodies are all typically made of 1 or more keys that are mapped to one or more values allowed.
//
// e.g.
// {
//     "StringEquals":                      <-- condition name
//     {                                    <-- body start
//         "key1": "value1",
//         "key2": ["value2", "value3"]
//     }                                    <-- body end
//
// }
//
// This is a shared implementation detail of concrete conditions
//
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub(in crate::conditions) struct Body<T>(pub(in crate::conditions) HashMap<String, ScalarOrSeq<T>>);

impl<T> Body<T> {
    /// Construct a new Body<T> with the initial key/value pair.
    pub fn new(k: String, v: T) -> Self {
        let mut body = Body(HashMap::new());
        body.insert(k, v);
        body
    }

    /// Insert a new key/value pair into this condition body. If the key already exists, the new
    /// value is appended to the list of acceptable values for that key
    pub fn insert(&mut self, k: String, v: T) {
        // replace the existing entry if it exists with a seq, or construct a new scalar
        let updated = match self.0.remove(&k) {
            Some(curr) => match curr {
                ScalarOrSeq::Scalar(sc) => ScalarOrSeq::Seq(vec![sc, v]),
                ScalarOrSeq::Seq(mut seq) => {
                    seq.push(v);
                    ScalarOrSeq::Seq(seq)
                }
            },
            None => ScalarOrSeq::Scalar(v),
        };

        self.0.insert(k, updated);
    }
}

/// A type that is able to evaluate whether the incoming (auth request) context passes some test (condition).
#[enum_dispatch(Condition)]
pub trait Eval {
    /// Evaluate if a condition is met for given request context
    fn evaluate(&self, ctx: &Context) -> bool;
}

/// Type Condition represents all of the possible conditions a policy (statement) is allowed to define.
/// A statement may contain more than one condition.
#[allow(missing_docs)] // Doc comments are broke with enum_dispatch
#[enum_dispatch]
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub enum Condition {
    StringEquals,
    StringNotEquals,
    StringEqualsIgnoreCase,
    StringNotEqualsIgnoreCase,
    StringLike,
    StringNotLike,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cond_body_json() {
        let jsp = r#"
        {
            "k1": "v1",
            "k2": ["v2", "v3"]
        }
        "#;

        let actual: Body<String> = serde_json::from_str(jsp).unwrap();
        let mut map = HashMap::new();
        map.insert("k1".to_owned(), ScalarOrSeq::Scalar("v1".to_owned()));
        map.insert(
            "k2".to_owned(),
            ScalarOrSeq::Seq(vec!["v2".to_owned(), "v3".to_owned()]),
        );
        let expected = Body(map);
        assert_eq!(expected, actual);

        let serialized = serde_json::to_string(&expected).unwrap();
        let expected1 = r#"{"k1":"v1","k2":["v2","v3"]}"#;
        let expected2 = r#"{"k2":["v2","v3"],"k1":"v1"}"#;
        assert!(
            serialized == expected1 || serialized == expected2,
            "serialized: {}",
            serialized
        );
    }

    #[test]
    fn test_scalar_or_seq_json() {
        // test scalar
        let jsp = r#"
            "myvalue"
        "#;

        let actual: ScalarOrSeq<String> = serde_json::from_str(jsp).unwrap();
        let expected: ScalarOrSeq<String> = ScalarOrSeq::Scalar("myvalue".to_owned());
        assert_eq!(expected, actual);

        let serialized = serde_json::to_string(&expected).unwrap();
        let expected = r#""myvalue""#;
        assert_eq!(expected, serialized);

        // test seq
        let jsp = r#"
            ["v1", "v2"]
        "#;

        let actual: ScalarOrSeq<String> = serde_json::from_str(jsp).unwrap();
        let expected: ScalarOrSeq<String> =
            ScalarOrSeq::Seq(vec!["v1".to_owned(), "v2".to_owned()]);
        assert_eq!(expected, actual);

        let serialized = serde_json::to_string(&expected).unwrap();
        let expected = r#"["v1","v2"]"#;
        assert_eq!(expected, serialized);

        // verify when embedded in map it works as expected
        let mut expected: HashMap<String, ScalarOrSeq<String>> = HashMap::new();
        let scalar = ScalarOrSeq::Scalar("v1".to_owned());
        let seq = ScalarOrSeq::Seq(vec!["v2".to_owned(), "v3".to_owned()]);
        expected.insert("foo".to_owned(), scalar);
        expected.insert("bar".to_owned(), seq);

        let jsp = r#"
        {
            "foo": "v1", 
            "bar": ["v2", "v3"]
        }
        "#;

        let actual: HashMap<String, ScalarOrSeq<String>> = serde_json::from_str(jsp).unwrap();
        assert_eq!(expected, actual);

        let serialized = serde_json::to_string(&expected).unwrap();
        let expected1 = r#"{"foo":"v1","bar":["v2","v3"]}"#;
        let expected2 = r#"{"bar":["v2","v3"],"foo":"v1"}"#;
        assert!(expected1 == serialized || expected2 == serialized);
    }

    #[test]
    fn test_body_insert() {
        let mut body = Body::new("k1".to_owned(), "v1".to_owned());

        let serialized = serde_json::to_string(&body).unwrap();
        let expected = r#"{"k1":"v1"}"#;
        assert_eq!(expected, serialized);

        body.insert("k1".to_owned(), "v2".to_owned());
        let serialized = serde_json::to_string(&body).unwrap();
        let expected = r#"{"k1":["v1","v2"]}"#;
        assert_eq!(expected, serialized);
    }

    #[test]
    fn test_cond_eval() {
        // test a condition.eval() works (via enum_dispatch) off the enum not just the concrete types
        let cond: Condition = StringEquals::new("k1", "v1").into();
        let mut ctx = Context::new();
        ctx.insert("k1", "v1");
        assert!(cond.evaluate(&ctx));
    }
}

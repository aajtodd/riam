use crate::Context;
use either::Either;
use enum_dispatch::enum_dispatch;
use serde::de::{self, Deserializer, Visitor};
use serde::ser::Serializer;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use std::iter::Iterator;

use super::string::{
    StringEquals, StringEqualsIgnoreCase, StringLike, StringNotEquals, StringNotEqualsIgnoreCase, StringNotLike,
};

/// Modifiers that change the way a condition evaluates the request context
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum EvalModifier {
    /// ForAllValues tests whether the value of every member of the request set is a subset of the condition key set.
    /// The condition returns true if every key value in the request matches at least one value in the policy. It also returns
    /// true if there are no keys in the request, or if the key values resolve to a null data set, such as an empty string.
    ForAllValues,

    /// ForAnyValue tests whether at least one member of the set of request values matches at least one member of the set of condition key values.
    /// The condition returns true if any one of the key values in the request matches any one of the condition values in the policy. For no matching
    /// key or a null dataset, the condition returns false
    ForAnyValue,

    /// IfExists modifies the condition such that if the key is present in the context of the request, process the key as specified in the policy.
    /// If the key is not present, evaluate the condition element as true.
    IfExists,
}

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

impl<T> ScalarOrSeq<T> {
    /// Allow conditions to iterate over the value or values without worrying about
    /// what variant it is.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        match *self {
            ScalarOrSeq::Scalar(ref sc) => Either::Left(std::iter::once(sc)),
            ScalarOrSeq::Seq(ref seq) => Either::Right(seq.iter()),
        }
    }
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
#[derive(Debug, PartialEq, Clone)]
pub enum Condition {
    StringEquals,
    StringNotEquals,
    StringEqualsIgnoreCase,
    StringNotEqualsIgnoreCase,
    StringLike,
    StringNotLike,
}

// The only way to get modifiers on the serialized format of a policy condition to match the syntax
// of AWS conditions is to implement custom serialization somewhere.
impl Serialize for Condition {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match *self {
            Condition::StringEquals(ref c) => {
                serializer.serialize_newtype_variant("Condition", 0, c.serialized_name(), c)
            }
            Condition::StringNotEquals(ref c) => {
                serializer.serialize_newtype_variant("Condition", 1, c.serialized_name(), c)
            }
            Condition::StringEqualsIgnoreCase(ref c) => {
                serializer.serialize_newtype_variant("Condition", 2, c.serialized_name(), c)
            }
            Condition::StringNotEqualsIgnoreCase(ref c) => {
                serializer.serialize_newtype_variant("Condition", 3, c.serialized_name(), c)
            }
            Condition::StringLike(ref c) => {
                serializer.serialize_newtype_variant("Condition", 4, c.serialized_name(), c)
            }
            Condition::StringNotLike(ref c) => {
                serializer.serialize_newtype_variant("Condition", 5, c.serialized_name(), c)
            }
        }
    }
}

// create a condition with an eval modifier set
macro_rules! de_cond_wmod {
    ( $t:ident, $m:ident, $modifier:ident) => {{
        let mut c: $t = $m.next_value()?;
        c.with_modifier(EvalModifier::$modifier);
        Ok(Condition::$t(c))
    }};
}

// delegate to the normal deserialization for a condition
macro_rules! de_cond {
    ( $t:ident, $m:ident) => {{
        Ok(Condition::$t($m.next_value::<$t>()?))
    }};
}

struct ConditionVisitor;

impl<'de> Visitor<'de> for ConditionVisitor {
    type Value = Condition;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a Condition")
    }

    fn visit_map<M>(self, mut map: M) -> Result<Self::Value, M::Error>
    where
        M: de::MapAccess<'de>,
    {
        let key: Option<&str> = map.next_key()?;
        if key.is_none() {
            return Err(de::Error::invalid_value(
                de::Unexpected::Str("missing condition name"),
                &self,
            ));
        }

        let key: &str = key.unwrap();
        match key {
            "StringEquals" => de_cond!(StringEquals, map),
            "IfExists:StringEquals" => de_cond_wmod!(StringEquals, map, IfExists),
            "ForAnyValue:StringEquals" => de_cond_wmod!(StringEquals, map, ForAnyValue),
            "ForAllValues:StringEquals" => de_cond_wmod!(StringEquals, map, ForAllValues),

            "StringNotEquals" => de_cond!(StringNotEquals, map),
            "IfExists:StringNotEquals" => de_cond_wmod!(StringNotEquals, map, IfExists),
            "ForAnyValue:StringNotEquals" => de_cond_wmod!(StringNotEquals, map, ForAnyValue),
            "ForAllValues:StringNotEquals" => de_cond_wmod!(StringNotEquals, map, ForAllValues),

            "StringEqualsIgnoreCase" => de_cond!(StringEqualsIgnoreCase, map),
            "IfExists:StringEqualsIgnoreCase" => de_cond_wmod!(StringEqualsIgnoreCase, map, IfExists),
            "ForAnyValue:StringEqualsIgnoreCase" => de_cond_wmod!(StringEqualsIgnoreCase, map, ForAnyValue),
            "ForAllValues:StringEqualsIgnoreCase" => de_cond_wmod!(StringEqualsIgnoreCase, map, ForAllValues),

            "StringNotEqualsIgnoreCase" => de_cond!(StringNotEqualsIgnoreCase, map),
            "IfExists:StringNotEqualsIgnoreCase" => de_cond_wmod!(StringNotEqualsIgnoreCase, map, IfExists),
            "ForAnyValue:StringNotEqualsIgnoreCase" => de_cond_wmod!(StringNotEqualsIgnoreCase, map, ForAnyValue),
            "ForAllValues:StringNotEqualsIgnoreCase" => de_cond_wmod!(StringNotEqualsIgnoreCase, map, ForAllValues),

            "StringLike" => de_cond!(StringLike, map),
            "IfExists:StringLike" => de_cond_wmod!(StringLike, map, IfExists),
            "ForAnyValue:StringLike" => de_cond_wmod!(StringLike, map, ForAnyValue),
            "ForAllValues:StringLike" => de_cond_wmod!(StringLike, map, ForAllValues),

            "StringNotLike" => de_cond!(StringNotLike, map),
            "IfExists:StringNotLike" => de_cond_wmod!(StringNotLike, map, IfExists),
            "ForAnyValue:StringNotLike" => de_cond_wmod!(StringNotLike, map, ForAnyValue),
            "ForAllValues:StringNotLike" => de_cond_wmod!(StringNotLike, map, ForAllValues),

            _ => Err(de::Error::invalid_value(
                de::Unexpected::Str("unrecognized condition type"),
                &self,
            )),
        }
    }
}

impl<'de> Deserialize<'de> for Condition {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(ConditionVisitor)
    }
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
        let expected: ScalarOrSeq<String> = ScalarOrSeq::Seq(vec!["v1".to_owned(), "v2".to_owned()]);
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

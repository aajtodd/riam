use crate::Context;
use enum_dispatch::enum_dispatch;
use serde::de::{self, Deserializer, Error, Visitor};
use serde::ser::{SerializeMap, Serializer};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use std::iter::Iterator;

use super::boolean::Bool;
use super::numeric::{
    NumericEquals, NumericGreaterThan, NumericGreaterThanEquals, NumericLessThan, NumericLessThanEquals,
    NumericNotEquals,
};
use super::{DateAfter, DateAtOrAfter, DateAtOrBefore, DateBefore, DateEquals, DateNotEquals};
use super::{
    StringEquals, StringEqualsIgnoreCase, StringLike, StringNotEquals, StringNotEqualsIgnoreCase, StringNotLike,
};
use super::{IpAddress, NotIpAddress};

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
#[derive(Debug, PartialEq, Clone)]
pub(in crate::conditions) struct Body<T>(pub(in crate::conditions) HashMap<String, Vec<T>>);

impl<T> Body<T> {
    /// Construct a new Body<T> with the initial key/value pair.
    pub fn new(k: String, v: T) -> Self {
        let mut body = Body(HashMap::new());
        body.insert(k, v);
        body
    }

    // TODO - maybe rename to push() and have an insert() method that actually does an inplace update or inserts new if it didn't exist
    /// Insert a new key/value pair into this condition body. If the key already exists, the new
    /// value is appended to the list of acceptable values for that key
    pub fn insert(&mut self, k: String, v: T) {
        self.0.entry(k).or_insert_with(Vec::new).push(v);
    }
}

impl<T> Serialize for Body<T>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.0.len()))?;
        for (k, v) in self.0.iter() {
            if v.len() == 1 {
                map.serialize_entry(&k, &v[0])?;
            } else {
                map.serialize_entry(&k, &v)?;
            }
        }
        map.end()
    }
}

impl<'de, T> Deserialize<'de> for Body<T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // deserialize through ScalarOrSeq which handles both cases then map to our target type
        let v = HashMap::<String, ScalarOrSeq<T>>::deserialize(deserializer)?;
        let body: HashMap<String, Vec<T>> = v
            .into_iter()
            .map(|(k, v)| match v {
                ScalarOrSeq::Scalar(sc) => (k, vec![sc]),
                ScalarOrSeq::Seq(seq) => (k, seq),
            })
            .collect();
        Ok(Body(body))
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
    Bool,
    NumericEquals,
    NumericNotEquals,
    NumericLessThan,
    NumericLessThanEquals,
    NumericGreaterThan,
    NumericGreaterThanEquals,
    DateEquals,
    DateNotEquals,
    DateBefore,
    DateAtOrBefore,
    DateAfter,
    DateAtOrAfter,
    IpAddress,
    NotIpAddress,
}

// The only way to get modifiers on the serialized format of a policy condition to match the syntax
// of AWS conditions is to implement custom serialization somewhere.
impl Serialize for Condition {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        macro_rules! ser_cond {
            ( $s:ident, $cond:ident, $idx:expr ) => {{
                $s.serialize_newtype_variant("Condition", $idx, $cond.serialized_name(), $cond)
            }};
        }
        match *self {
            Condition::StringEquals(ref c) => ser_cond!(serializer, c, 0),
            Condition::StringNotEquals(ref c) => ser_cond!(serializer, c, 1),
            Condition::StringEqualsIgnoreCase(ref c) => ser_cond!(serializer, c, 2),
            Condition::StringNotEqualsIgnoreCase(ref c) => ser_cond!(serializer, c, 3),
            Condition::StringLike(ref c) => ser_cond!(serializer, c, 4),
            Condition::StringNotLike(ref c) => ser_cond!(serializer, c, 5),
            Condition::Bool(ref c) => ser_cond!(serializer, c, 6),
            Condition::NumericEquals(ref c) => ser_cond!(serializer, c, 7),
            Condition::NumericNotEquals(ref c) => ser_cond!(serializer, c, 8),
            Condition::NumericLessThan(ref c) => ser_cond!(serializer, c, 9),
            Condition::NumericLessThanEquals(ref c) => ser_cond!(serializer, c, 10),
            Condition::NumericGreaterThan(ref c) => ser_cond!(serializer, c, 11),
            Condition::NumericGreaterThanEquals(ref c) => ser_cond!(serializer, c, 12),
            Condition::DateEquals(ref c) => ser_cond!(serializer, c, 13),
            Condition::DateNotEquals(ref c) => ser_cond!(serializer, c, 14),
            Condition::DateBefore(ref c) => ser_cond!(serializer, c, 15),
            Condition::DateAtOrBefore(ref c) => ser_cond!(serializer, c, 16),
            Condition::DateAfter(ref c) => ser_cond!(serializer, c, 17),
            Condition::DateAtOrAfter(ref c) => ser_cond!(serializer, c, 18),
            Condition::IpAddress(ref c) => ser_cond!(serializer, c, 19),
            Condition::NotIpAddress(ref c) => ser_cond!(serializer, c, 20),
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

            "Bool" => de_cond!(Bool, map),
            "IfExists:Bool" => {
                let mut c = map.next_value::<Bool>()?;
                c.set_if_exists();
                Ok(Condition::Bool(c))
            }

            "NumericEquals" => de_cond!(NumericEquals, map),
            "IfExists:NumericEquals" => de_cond_wmod!(NumericEquals, map, IfExists),
            "ForAnyValue:NumericEquals" => de_cond_wmod!(NumericEquals, map, ForAnyValue),
            "ForAllValues:NumericEquals" => de_cond_wmod!(NumericEquals, map, ForAllValues),

            "NumericNotEquals" => de_cond!(NumericNotEquals, map),
            "IfExists:NumericNotEquals" => de_cond_wmod!(NumericNotEquals, map, IfExists),
            "ForAnyValue:NumericNotEquals" => de_cond_wmod!(NumericNotEquals, map, ForAnyValue),
            "ForAllValues:NumericNotEquals" => de_cond_wmod!(NumericNotEquals, map, ForAllValues),

            "NumericLessThan" => de_cond!(NumericLessThan, map),
            "IfExists:NumericLessThan" => de_cond_wmod!(NumericLessThan, map, IfExists),
            "ForAnyValue:NumericLessThan" => de_cond_wmod!(NumericLessThan, map, ForAnyValue),
            "ForAllValues:NumericLessThan" => de_cond_wmod!(NumericLessThan, map, ForAllValues),

            "NumericLessThanEquals" => de_cond!(NumericLessThanEquals, map),
            "IfExists:NumericLessThanEquals" => de_cond_wmod!(NumericLessThanEquals, map, IfExists),
            "ForAnyValue:NumericLessThanEquals" => de_cond_wmod!(NumericLessThanEquals, map, ForAnyValue),
            "ForAllValues:NumericLessThanEquals" => de_cond_wmod!(NumericLessThanEquals, map, ForAllValues),

            "NumericGreaterThan" => de_cond!(NumericGreaterThan, map),
            "IfExists:NumericGreaterThan" => de_cond_wmod!(NumericGreaterThan, map, IfExists),
            "ForAnyValue:NumericGreaterThan" => de_cond_wmod!(NumericGreaterThan, map, ForAnyValue),
            "ForAllValues:NumericGreaterThan" => de_cond_wmod!(NumericGreaterThan, map, ForAllValues),

            "NumericGreaterThanEquals" => de_cond!(NumericGreaterThanEquals, map),
            "IfExists:NumericGreaterThanEquals" => de_cond_wmod!(NumericGreaterThanEquals, map, IfExists),
            "ForAnyValue:NumericGreaterThanEquals" => de_cond_wmod!(NumericGreaterThanEquals, map, ForAnyValue),
            "ForAllValues:NumericGreaterThanEquals" => de_cond_wmod!(NumericGreaterThanEquals, map, ForAllValues),

            "DateEquals" => de_cond!(DateEquals, map),
            "IfExists:DateEquals" => de_cond_wmod!(DateEquals, map, IfExists),
            "ForAnyValue:DateEquals" => de_cond_wmod!(DateEquals, map, ForAnyValue),
            "ForAllValues:DateEquals" => de_cond_wmod!(DateEquals, map, ForAllValues),

            "DateNotEquals" => de_cond!(DateNotEquals, map),
            "IfExists:DateNotEquals" => de_cond_wmod!(DateNotEquals, map, IfExists),
            "ForAnyValue:DateNotEquals" => de_cond_wmod!(DateNotEquals, map, ForAnyValue),
            "ForAllValues:DateNotEquals" => de_cond_wmod!(DateNotEquals, map, ForAllValues),

            "DateBefore" => de_cond!(DateBefore, map),
            "IfExists:DateBefore" => de_cond_wmod!(DateBefore, map, IfExists),
            "ForAnyValue:DateBefore" => de_cond_wmod!(DateBefore, map, ForAnyValue),
            "ForAllValues:DateBefore" => de_cond_wmod!(DateBefore, map, ForAllValues),

            "DateAtOrBefore" => de_cond!(DateAtOrBefore, map),
            "IfExists:DateAtOrBefore" => de_cond_wmod!(DateAtOrBefore, map, IfExists),
            "ForAnyValue:DateAtOrBefore" => de_cond_wmod!(DateAtOrBefore, map, ForAnyValue),
            "ForAllValues:DateAtOrBefore" => de_cond_wmod!(DateAtOrBefore, map, ForAllValues),

            "DateAfter" => de_cond!(DateAfter, map),
            "IfExists:DateAfter" => de_cond_wmod!(DateAfter, map, IfExists),
            "ForAnyValue:DateAfter" => de_cond_wmod!(DateAfter, map, ForAnyValue),
            "ForAllValues:DateAfter" => de_cond_wmod!(DateAfter, map, ForAllValues),

            "DateAtOrAfter" => de_cond!(DateAtOrAfter, map),
            "IfExists:DateAtOrAfter" => de_cond_wmod!(DateAtOrAfter, map, IfExists),
            "ForAnyValue:DateAtOrAfter" => de_cond_wmod!(DateAtOrAfter, map, ForAnyValue),
            "ForAllValues:DateAtOrAfter" => de_cond_wmod!(DateAtOrAfter, map, ForAllValues),

            "IpAddress" => de_cond!(IpAddress, map),
            "IfExists:IpAddress" => de_cond_wmod!(IpAddress, map, IfExists),
            "ForAnyValue:IpAddress" => de_cond_wmod!(IpAddress, map, ForAnyValue),
            "ForAllValues:IpAddress" => de_cond_wmod!(IpAddress, map, ForAllValues),

            "NotIpAddress" => de_cond!(NotIpAddress, map),
            "IfExists:NotIpAddress" => de_cond_wmod!(NotIpAddress, map, IfExists),
            "ForAnyValue:NotIpAddress" => de_cond_wmod!(NotIpAddress, map, ForAnyValue),
            "ForAllValues:NotIpAddress" => de_cond_wmod!(NotIpAddress, map, ForAllValues),

            _ => {
                let msg = format!("unrecognized condition '{}'", key);
                Err(de::Error::invalid_value(de::Unexpected::Str(&msg), &self))
            }
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
        // test that body deserializes/serializes with both scalar and seq values
        let jsp = r#"
        {
            "k1": "v1",
            "k2": ["v2", "v3"]
        }
        "#;

        let actual: Body<String> = serde_json::from_str(jsp).unwrap();
        let mut map: HashMap<String, Vec<String>> = HashMap::new();
        map.insert("k1".to_owned(), vec!["v1".to_owned()]);
        map.insert("k2".to_owned(), vec!["v2".to_owned(), "v3".to_owned()]);
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

    #[test]
    fn test_invalid_cond_json() {
        let jsp = r#"
            {
                "unknown": {
                    "mykey": "myvalue"
                }
            }
        "#;

        let actual: Result<Condition, serde_json::Error> = serde_json::from_str(jsp);
        assert!(actual.is_err());
    }
}

//! Policy Conditions

use serde::de::{Deserializer, MapAccess, Visitor};
use serde::ser::Serializer;
use serde::{Deserialize, Serialize};
use serde_json::Number;
use std::collections::HashMap;
use std::fmt;
use std::marker::PhantomData;

// TODO - ideally we wouldn't be constrained to just key/value context but deserializing arbitrary
// JSON into Map<String, serde_json::Value> is going to be more difficult to deal with. For now
// let's get this library working even if it comes with some caveats.
/// Authorization request context. Consists of key/value pairs that the caller is expected to
/// gather and send with a request to enable condition evaluation. A policy that has conditions
/// will fail if the context is missing.
struct Context(HashMap<String, String>);

trait Eval {
    /// Evaluate if a condition is met for given request context
    fn evaluate(&self, ctx: &Context) -> bool;
}

/*

   FIXME - this design for conditions falls apart....

From AWS IAM:
If your policy has multiple condition operators or multiple keys attached to a single condition operator, the conditions are evaluated using a logical AND. If a single condition operator includes multiple values for one key, that condition operator is evaluated using a logical OR. All conditions must resolve to true to trigger the desired Allow or Deny effect.


example:

- The "StringEquals" and the "DateBefore" are AND'd together.
- The "StringEquals" "key1" and "key2" conditions are AND'd together (both key1 and key2 must match)
- The "StringEquals" "key2" condition can be either "value1" or "value2"

   "StringEquals": {
       "key1": "value1",
            AND
       "key2": ["value2, value3"]      <-- OR'd together. key2 can be any of those values
   },

            AND

   "DateBefore": {
       "aws:currentTime": "2019/07/22:00:00:00Z"
   }

----------------------------------

   struct StringEquals {
       inner: HashMap<String, Vec<String>>
       OR
       inner: HashMap<String, serde_json::Value>
   }

   fn evaluate(&self, ctx: &Context) -> bool {
       // for each key, check if any of the values match
   }


 */

// To get the resulting JSON syntax we want for conditions we either
// have to (a) implement a custom parser that understands the different
// key names or (b) use serde's support for enums at the tradeoff of not
// having dynamic dispatch.
//
// We are going to go with the enum approach for now since it simplifies
// the serialization considerably and there is a crate
// [enum_dispatch](https://gitlab.com/antonok/enum_dispatch) that
// implements the "dynamic" dispatch for us. It has the added benefit
// of likely being faster and not requiring a heap allocation.

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
enum Condition {
    StringEquals(StringEquals),
    StringNotEquals(StringNotEquals),
}

#[derive(Debug, Clone, PartialEq)]
struct StringEquals {
    key: String,
    value: String,
}

impl Eval for StringEquals {
    fn evaluate(&self, ctx: &Context) -> bool {
        ctx.0
            .get(&self.key)
            .and_then(|x| Some(*x == self.value))
            .unwrap_or(false)
    }
}

#[derive(PartialEq, Debug, Clone)]
struct StringNotEquals {
    key: String,
    value: String,
}

// Generic visitor for any of our simple conditions that consist of only a key/value pair
struct StructMapVisitor<T> {
    marker: PhantomData<fn() -> T>,
}

impl<T> StructMapVisitor<T> {
    fn new() -> Self {
        StructMapVisitor {
            marker: PhantomData,
        }
    }
}

// StructMap contains functions that allow the generic visitor to work on simple key:value pair types
trait StructMap {
    type K;
    type V;

    // create a new instance of the concrete type with the key/value pair
    fn new(key: Self::K, value: Self::V) -> Self;

    // the name of the type (e.g. "StringEquals").
    fn type_name() -> &'static str;
}

impl<'de, T, K, V> Visitor<'de> for StructMapVisitor<T>
where
    K: Deserialize<'de>,
    V: Deserialize<'de>,
    T: StructMap<K = K, V = V>,
{
    // The type that our Visitor is going to produce.
    type Value = T;

    // Format a message stating what data this Visitor expects to receive.
    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str(T::type_name())
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: MapAccess<'de>,
    {
        // FIXME - remove this unwrap
        let (key, value) = access.next_entry()?.unwrap();
        let cond = T::new(key, value);

        Ok(cond)
    }
}

// Implement Serialize/Deserialize for simple structs that have a key/value pair
// A StructMap type is any type with a (key,value) field names that will be
// serialized as {"k": "v"} where `k` and `v` are the actual values not the field names.
// Normal serialization for a struct with field names 'key' and 'value' would otherwise
// look like {"key": "k", "value": "v"}
macro_rules! impl_serde_struct_map {
    ($t:ident, $k:ident, $v:ident) => {
        impl StructMap for $t {
            type K = $k;
            type V = $v;

            fn new(k: Self::K, v: Self::V) -> $t {
                $t { key: k, value: v }
            }

            fn type_name() -> &'static str {
                stringify!($t)
            }
        }

        impl Serialize for $t {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                use serde::ser::SerializeMap;
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry(&self.key, &self.value)?;
                map.end()
            }
        }

        impl<'de> Deserialize<'de> for $t {
            fn deserialize<D>(deserializer: D) -> Result<$t, D::Error>
            where
                D: Deserializer<'de>,
            {
                deserializer.deserialize_map(StructMapVisitor::<$t>::new())
            }
        }
    };
}

impl_serde_struct_map!(StringEquals, String, String);
impl_serde_struct_map!(StringNotEquals, String, String);

struct StringEqualsIgnoreCase {
    key: String,
    value: String,
}
struct StringNotEqualsIgnoreCase {
    key: String,
    value: String,
}
struct StringLike {
    key: String,
    value: String,
}
struct StringNotLIke {
    key: String,
    value: String,
}

struct BoolCondition {
    key: String,
    value: bool,
}

struct NumericEquals {
    key: String,
    value: Number,
}
struct NumericNotEquals {
    key: String,
    value: Number,
}
struct NumericLessThan {
    key: String,
    value: Number,
}
struct NumericLessThanEquals {
    key: String,
    value: Number,
}
struct NumericGreaterThan {
    key: String,
    value: Number,
}
struct NumericGreaterThanEquals {
    key: String,
    value: Number,
}

// TODO - use chrono for datetime
// struct DateEquals{key: String, value: DateTime};
// struct DateNotEquals{key: String, value: DateTime};
// struct DateBefore{key: String, value: DateTime};
// struct DateAfter{key: String, value: DateTime};
// struct DateBeforeExact{key: String, value: DateTime};
// struct DateAfterExact{key: String, value: DateTime};

// TODO - see Rust CIDR crate for dealing with IP ranges

// TODO - evaluate what if any builtin keys we might provide. e.g. riam:CurrentTime or ${currentTime}, riam:principal

#[cfg(test)]
mod tests {
    use super::*;

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
        let expected = Condition::StringEquals(StringEquals {
            key: "mykey".to_owned(),
            value: "myvalue".to_owned(),
        });
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
        let expected = Condition::StringNotEquals(StringNotEquals {
            key: "mykey".to_owned(),
            value: "myvalue".to_owned(),
        });
        assert_eq!(expected, actual);

        let serialized = serde_json::to_string(&expected).unwrap();
        let expected = r#"{"StringNotEquals":{"mykey":"myvalue"}}"#;
        assert_eq!(expected, serialized);

        assert_eq!("StringNotEquals", StringNotEquals::type_name());
    }

    #[test]
    fn test_eval_string_equals() {
        let cond = StringEquals {
            key: "mykey".to_owned(),
            value: "myvalue".to_owned(),
        };

        let mut ctx = Context(HashMap::new());
        ctx.0.insert("mykey".to_owned(), "myvalue".to_owned());

        assert!(cond.evaluate(&ctx));

        ctx.0.insert("mykey".to_owned(), "myvalue2".to_owned());
        assert!(!cond.evaluate(&ctx));
    }
}

// FIXME - leftoff figuring out if I like this macro implementation
// Basically will require implementing a trait Eval{...} specific to each condition and then just
// adding the macro call

/*

"condition:" {
    "StringEquals": {
        "key": "value"
    }
}

e.g.:

"condition": {
    "StringEquals": {
        "UserAgent": "Example Corp Java Client"
    }
}

would match the request:

{
    "principal": "user1",
    "action": "some-action",
    "resource": "some-resource",
    "context": {
        "UserAgent": "Example Corp Java Client"
    }

}

*/

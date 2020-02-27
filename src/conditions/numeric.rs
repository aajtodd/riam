/// Numeric condition operators let you construct Condition elements that restrict access based on comparing a key to an integer or decimal value.
use super::condition::{Body, EvalModifier};
use super::Eval;
use crate::Context;
use rust_decimal::prelude::FromPrimitive;
use rust_decimal::Decimal;
use serde::de::Unexpected;
use serde::{Deserialize, Serialize};
use std::cmp;
use std::fmt;
use std::str::FromStr;

// TODO - move this to common and implement string using it.
// TODO - rename body::insert to body::push. Add an insert() method that does a replace inplace
// like HashMap::insert
macro_rules! impl_cond_base {
    ($x:ident, $body_ty:tt, $sname:expr) => {
        impl $x {
            /// Create a new condition with initial key/value pair
            pub fn new<K, V>(key: K, value: V) -> Self
            where
                K: Into<String>,
                V: Into<$body_ty>,
            {
                $x {
                    modifier: None,
                    body: Body::new(key.into(), value.into()),
                }
            }

            // FIXME - the generated documentation (and doctest) will use the same example/type
            // regardless of the type passed to the macro
            /// Add additional key/value pairs. If the key already exists the
            /// value is appended to the list of allowed values for this key.
            pub fn push<'a, K, V>(&'a mut self, key: K, value: V) -> &'a Self
            where
                K: Into<String>,
                V: Into<$body_ty>,
            {
                self.body.insert(key.into(), value.into());
                self
            }

            /// The name that should be used to serialize this condition.
            /// Modifiers like ForAllValues, ForAnyValue, and IfExists can change
            /// the expected serialized name.
            pub(crate) fn serialized_name(&self) -> &'static str {
                match self.modifier {
                    Some(EvalModifier::ForAllValues) => concat!("ForAllValues:", $sname),
                    Some(EvalModifier::ForAnyValue) => concat!("ForAnyValue:", $sname),
                    Some(EvalModifier::IfExists) => concat!("IfExists:", $sname),
                    None => $sname,
                }
            }

            /// Modify the way this condition is evaluated. Only one modifier is set at a time,
            /// you can't combine them.
            pub fn with_modifier(&mut self, m: EvalModifier) {
                self.modifier = Some(m);
            }
        }
    };

    ($name:tt, $body_ty:tt) => {
        impl_cond_base!($name, $body_ty, stringify!($name));
    };
}

// Represents both integer or fixed point decimal numbers. Derived from implemenation of
// serde_json::Value.
#[derive(Debug, Clone, Copy)]
pub enum Num {
    PosInt(u64),
    NegInt(i64),
    Decimal(Decimal),
}

impl serde::Serialize for Num {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match *self {
            Num::PosInt(u) => serializer.serialize_u64(u),
            Num::NegInt(i) => serializer.serialize_i64(i),
            Num::Decimal(d) => serde::Serialize::serialize(&d, serializer),
        }
    }
}

impl<'de> serde::Deserialize<'de> for Num {
    fn deserialize<D>(deserializer: D) -> Result<Num, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        deserializer.deserialize_any(NumVisitor)
    }
}

struct NumVisitor;

impl<'de> serde::de::Visitor<'de> for NumVisitor {
    type Value = Num;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "integer or fixed point decimal")
    }

    fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(value.into())
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(value.into())
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        let d = Decimal::from_str(value).map_err(|_| E::invalid_value(Unexpected::Str(value), &self))?;
        Ok(d.into())
    }

    fn visit_f64<E>(self, value: f64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        let d = Decimal::from_f64(value).ok_or_else(|| E::invalid_value(Unexpected::Float(value), &self))?;
        Ok(d.into())
    }
}

macro_rules! impl_from_unsigned {
    (
        $($ty:ty),*
    ) => {
        $(
            impl From<$ty> for Num {
                #[inline]
                fn from(u: $ty) -> Self {
                     Num::PosInt(u as u64)
                }
            }
        )*
    };
}

macro_rules! impl_from_signed {
    (
        $($ty:ty),*
    ) => {
        $(
            impl From<$ty> for Num {
                #[inline]
                fn from(i: $ty) -> Self {
                    if i < 0 {
                        Num::NegInt(i as i64)
                    } else {
                        Num::PosInt(i as u64)
                    }
                }
            }
        )*
    };
}

impl_from_unsigned!(u8, u16, u32, u64, usize);
impl_from_signed!(i8, i16, i32, i64, isize);

// TODO From i128/u128 and from/try_from f32/f64

impl From<Decimal> for Num {
    fn from(d: Decimal) -> Self {
        Num::Decimal(d)
    }
}

impl Into<Decimal> for Num {
    fn into(self) -> Decimal {
        match self {
            Num::NegInt(i) => i.into(),
            Num::PosInt(u) => u.into(),
            Num::Decimal(d) => d,
        }
    }
}

// copies are a bit heavy handed but it drastically simplifies the implementation. Leverage
// decimal implementation of PartialEq/Eq and PartialOrd/Ord
impl cmp::PartialEq for Num {
    fn eq(&self, other: &Self) -> bool {
        let d1: Decimal = (*self).into();
        let d2: Decimal = (*other).into();
        d1.eq(&d2)
    }
}

impl cmp::Eq for Num {}

impl cmp::PartialOrd for Num {
    fn partial_cmp(&self, other: &Num) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl cmp::Ord for Num {
    fn cmp(&self, other: &Num) -> cmp::Ordering {
        let d1: Decimal = (*self).into();
        let d2: Decimal = (*other).into();
        d1.cmp(&d2)
    }
}

/// Exact matching
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct NumericEquals {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<Num>,
}

impl_cond_base!(NumericEquals, Num);

impl Eval for NumericEquals {
    fn evaluate(&self, ctx: &Context) -> bool {
        // TODO - are numeric conditions really able to have multiple values??
        unimplemented!()
    }
}

/// Negated matching
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct NumericNotEquals {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<Num>,
}

impl_cond_base!(NumericNotEquals, Num);

impl Eval for NumericNotEquals {
    fn evaluate(&self, ctx: &Context) -> bool {
        unimplemented!()
    }
}

/// Less than ("<") matching
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct NumericLessThan {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<Num>,
}

impl_cond_base!(NumericLessThan, Num);

impl Eval for NumericLessThan {
    fn evaluate(&self, ctx: &Context) -> bool {
        unimplemented!()
    }
}

/// Less than or equal ("<=") matching
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct NumericLessThanEquals {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<Num>,
}

impl_cond_base!(NumericLessThanEquals, Num);

impl Eval for NumericLessThanEquals {
    fn evaluate(&self, ctx: &Context) -> bool {
        unimplemented!()
    }
}

/// Greater than (">") matching
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct NumericGreaterThan {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<Num>,
}

impl_cond_base!(NumericGreaterThan, Num);

impl Eval for NumericGreaterThan {
    fn evaluate(&self, ctx: &Context) -> bool {
        unimplemented!()
    }
}

/// Greater than or equal (">=") matching
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct NumericGreaterThanEquals {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<Num>,
}

impl_cond_base!(NumericGreaterThanEquals, Num);

impl Eval for NumericGreaterThanEquals {
    fn evaluate(&self, ctx: &Context) -> bool {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::super::*;
    use super::*;

    #[test]
    fn test_num_serialize() {
        let tests = [
            (Num::PosInt(2), "2"),
            (Num::NegInt(-7), "-7"),
            (Num::Decimal(Decimal::new(202, 2)), "\"2.02\""),
        ];

        for (value, expected) in tests.iter() {
            let actual = serde_json::to_string(&value).unwrap();
            assert_eq!(expected, &actual);
        }
    }

    #[test]
    fn test_num_deserialize() {
        let tests = [
            ("2", Num::PosInt(2)),
            ("-7", Num::NegInt(-7)),
            ("\"2.02\"", Num::Decimal(Decimal::new(202, 2))),
            ("12.02", Num::Decimal(Decimal::new(1202, 2))),
        ];

        for (value, expected) in tests.iter() {
            let actual: Num = serde_json::from_str(&value).unwrap();
            assert_eq!(*expected, actual);
        }
    }

    #[test]
    fn test_num_ops() {
        let (x, y) = (Num::PosInt(2), Num::NegInt(-7));
        assert!(x > y);

        let d: Decimal = (-7i64).into();
        let (x, y) = (Num::Decimal(d), Num::NegInt(-7));
        assert!(x == y);
    }

    macro_rules! json_test {
        ( $t:ident, $sname:expr ) => {{
            // e.g. { "StringEquals": { "mykey": "myvalue" } }
            let jsp = format!("{{\"{}\": {{\"k1\":17}}}}", $sname);

            let actual: Condition = serde_json::from_str(&jsp).unwrap();
            let expected = Condition::$t($t::new("k1", 17));
            assert_eq!(expected, actual);

            let serialized = serde_json::to_string(&expected).unwrap();
            // e.g. {"StringEquals":{"mykey":"myvalue"}}
            let expected = format!("{{\"{}\":{{\"k1\":17}}}}", $sname);
            assert_eq!(expected, serialized);
        }};

        ( $t:ident ) => {
            json_test!($t, stringify!($t))
        };
    }

    #[test]
    fn test_numeric_equals_json() {
        json_test!(NumericEquals);
    }

    #[test]
    fn test_numeric_not_equals_json() {
        json_test!(NumericNotEquals);
    }

    #[test]
    fn test_numeric_less_than() {
        json_test!(NumericLessThan);
    }

    #[test]
    fn test_numeric_less_than_equals() {
        json_test!(NumericLessThanEquals);
    }

    #[test]
    fn test_numeric_greater_than() {
        json_test!(NumericGreaterThan);
    }

    #[test]
    fn test_numeric_greater_than_equals() {
        json_test!(NumericGreaterThanEquals);
    }

    #[test]
    fn test_serialized_name() {
        // same impl across all Numeric* condition types
        let mut cond = NumericEquals::new("k1", 17);
        assert_eq!(cond.serialized_name(), "NumericEquals");

        cond.with_modifier(EvalModifier::ForAnyValue);
        assert_eq!(cond.serialized_name(), "ForAnyValue:NumericEquals");

        cond.with_modifier(EvalModifier::ForAllValues);
        assert_eq!(cond.serialized_name(), "ForAllValues:NumericEquals");

        cond.with_modifier(EvalModifier::IfExists);
        assert_eq!(cond.serialized_name(), "IfExists:NumericEquals");
    }

    #[test]
    fn test_numeric_cond_deserialize_with_eval_modifier() {
        // catch all test for deserialization with modifiers, necessary because of our switch
        // to custom serialization/deserialization logic to enable IAM like syntax of serialized policies
        let jsp = r#"
        [
            {"ForAnyValue:NumericEquals": {"k": 17}},
            {"ForAllValues:NumericEquals": {"k": 17}},
            {"IfExists:NumericEquals": {"k": 17}},
            {"ForAnyValue:NumericNotEquals": {"k": 17}},
            {"ForAllValues:NumericNotEquals": {"k": 17}},
            {"IfExists:NumericNotEquals": {"k": 17}},
            {"ForAnyValue:NumericLessThan": {"k": 17}},
            {"ForAllValues:NumericLessThan": {"k": 17}},
            {"IfExists:NumericLessThan": {"k": 17}},
            {"ForAnyValue:NumericLessThanEquals": {"k": 17}},
            {"ForAllValues:NumericLessThanEquals": {"k": 17}},
            {"IfExists:NumericLessThanEquals": {"k": 17}},
            {"ForAnyValue:NumericGreaterThan": {"k": 17}},
            {"ForAllValues:NumericGreaterThan": {"k": 17}},
            {"IfExists:NumericGreaterThan": {"k": 17}},
            {"ForAnyValue:NumericGreaterThanEquals": {"k": 17}},
            {"ForAllValues:NumericGreaterThanEquals": {"k": 17}},
            {"IfExists:NumericGreaterThanEquals": {"k": 17}}
        ]
        "#;

        // create a condition with an eval modifier set for this test
        macro_rules! new_cond {
            ( $t:ident, $modifier:ident) => {{
                let mut c = $t::new("k", 17);
                c.with_modifier(EvalModifier::$modifier);
                Condition::$t(c)
            }};
        }

        let actual: Vec<Condition> = serde_json::from_str(jsp).unwrap();
        let expected = vec![
            new_cond!(NumericEquals, ForAnyValue),
            new_cond!(NumericEquals, ForAllValues),
            new_cond!(NumericEquals, IfExists),
            new_cond!(NumericNotEquals, ForAnyValue),
            new_cond!(NumericNotEquals, ForAllValues),
            new_cond!(NumericNotEquals, IfExists),
            new_cond!(NumericLessThan, ForAnyValue),
            new_cond!(NumericLessThan, ForAllValues),
            new_cond!(NumericLessThan, IfExists),
            new_cond!(NumericLessThanEquals, ForAnyValue),
            new_cond!(NumericLessThanEquals, ForAllValues),
            new_cond!(NumericLessThanEquals, IfExists),
            new_cond!(NumericGreaterThan, ForAnyValue),
            new_cond!(NumericGreaterThan, ForAllValues),
            new_cond!(NumericGreaterThan, IfExists),
            new_cond!(NumericGreaterThanEquals, ForAnyValue),
            new_cond!(NumericGreaterThanEquals, ForAllValues),
            new_cond!(NumericGreaterThanEquals, IfExists),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_eval_numeric_equals() {
        // integer
        // singular
        // let cond = NumericEquals::new("k1", 17);
        //
        // let mut ctx = Context::new();
        // ctx.insert("k1", 17);
        //
        // assert!(cond.evaluate(&ctx));
        //
        // ctx.insert("k1", 5);
        // assert!(!cond.evaluate(&ctx));
        //
        // // multiple
        // let mut cond = NumericEquals::new("k1", 17);
        // cond.push("k1", 2);
        // ctx.insert("k1", 2);
        // assert!(cond.evaluate(&ctx));
        //
        // ctx.insert("k1", 5);
        // assert!(!cond.evaluate(&ctx));

        // TODO float/decimal
    }
}

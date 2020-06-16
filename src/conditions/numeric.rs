/// Numeric condition operators let you construct Condition elements that restrict access based on comparing a key to an integer or decimal value.
use super::condition::{Body, EvalModifier, ScalarOrSeq};
use super::{util, Eval};
use crate::Context;
use rust_decimal::prelude::FromPrimitive;
use rust_decimal::Decimal;
use serde::de::Unexpected;
use serde::{Deserialize, Serialize};
use std::cmp;
use std::convert::TryFrom;
use std::fmt;
use std::str::FromStr;

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

impl TryFrom<serde_json::Value> for Num {
    type Error = serde_json::Error;

    fn try_from(value: serde_json::Value) -> Result<Self, Self::Error> {
        let n: Num = serde_json::from_value(value)?;
        Ok(n)
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

// convert a JSON value to a vec handling both scalar and seq types (e.g. "v1" and ["v1", "v2"])
fn serde_json_value_to_vec(v: serde_json::Value) -> Result<Vec<Num>, serde_json::Error> {
    let x: ScalarOrSeq<Num> = serde_json::from_value(v)?;
    let seq = match x {
        ScalarOrSeq::Scalar(s) => vec![s],
        ScalarOrSeq::Seq(seq) => seq,
    };
    Ok(seq)
}

macro_rules! eval_num_cond {
    ($cond:ident, $ctx:ident, $cmp:expr) => {{
        // use the same comparison lambda for both forall/forany as well as the singular case
        eval_num_cond!($cond, $ctx, $cmp, $cmp)
    }};

    // condition, context, lambda used for comparison (plural), lambda used for comparison (singular)
    // Lambda will be passed (condv, ctxv) and should yield a boolean result.
    //
    // ... why the distinction you ask. Well the signatures of for_any_match, is_subset, etc do not
    // match the signature of the singular case (e.g. &String vs &str). I'm sure there is a way around
    // this but I haven't seen a clean way that keeps the functions generic over any type T without
    // be more specific and specifying &str (which would fix the ambiguity and difference between
    // the two cases). For now allow the closures to be specified independently *if needed*.
    ($cond:ident, $ctx:ident, $cmp:expr, $scmp:expr) => {{
        let default = match $cond.modifier {
            Some(EvalModifier::IfExists) => true,
            _ => false,
        };

        for (key, cond_values) in $cond.body.0.iter() {
            let valid = $ctx
                .get(key)
                .and_then(|x| {
                    match $cond.modifier {
                        Some(EvalModifier::ForAllValues) => {
                            // all the incoming request context values for the key need to be a subset
                            // of the condition values
                            let ctx_values = serde_json_value_to_vec(x.clone()).ok().unwrap_or_else(Vec::new);
                            Some(util::is_subset(cond_values, ctx_values.as_slice(), $cmp))
                        }
                        Some(EvalModifier::ForAnyValue) => {
                            // at least one of the context values has to match a condition value
                            let ctx_values = serde_json_value_to_vec(x.clone()).ok().unwrap_or_else(Vec::new);
                            Some(util::intersects(cond_values, ctx_values.as_slice(), $cmp))
                        }
                        // possible (cond) value's are OR'd together for evaluation (only 1 needs to pass)
                        // context is expected to be scalar. If it is a sequence the conditions
                        // should be using set modifiers
                        _ => {
                            match Num::try_from(x.clone()) {
                                Ok(v) => Some(cond_values.iter().any(|n| {
                                    let result = $scmp(n, &v);
                                    result
                                })),
                                // it is important that if conversion from Value -> Num fails None that we don't use the
                                // default. It should be false no matter what if the conversion fails
                                // as we are expecting some kind of number here AND the key did exist. This mostly
                                // affects IfExists where the default is true
                                Err(_) => Some(false),
                            }
                        }
                    }
                })
                .unwrap_or(default);

            // all keys are and'd together to pass the condition, short-circuit early if one doesn't pass
            if !valid {
                return false;
            }
        }
        true
    }};
}

macro_rules! eval_num_not_cond {
    ($cond:ident, $ctx:ident, $cmp:expr) => {{
        eval_num_not_cond!($cond, $ctx, $cmp, $cmp)
    }};

    ($cond:ident, $ctx:ident, $cmp:expr, $scmp:expr) => {{
        let default = match $cond.modifier {
            Some(EvalModifier::IfExists) => true,
            _ => false,
        };

        for (key, cond_values) in $cond.body.0.iter() {
            let valid = $ctx
                .get(key)
                .and_then(|x| match $cond.modifier {
                    Some(EvalModifier::ForAllValues) => {
                        let ctx_values = serde_json_value_to_vec(x.clone()).ok().unwrap_or_else(Vec::new);
                        Some(util::is_disjoint(cond_values, ctx_values.as_slice(), $cmp))
                    }
                    Some(EvalModifier::ForAnyValue) => {
                        let ctx_values = serde_json_value_to_vec(x.clone()).ok().unwrap_or_else(Vec::new);
                        Some(util::intersects(cond_values, ctx_values.as_slice(), |x, y| {
                            !($cmp(x, y))
                        }))
                    }
                    _ => match Num::try_from(x.clone()) {
                        Ok(v) => Some(cond_values.iter().any(|n| {
                            let result = $scmp(n, &v);
                            !result
                        })),
                        Err(_) => Some(false),
                    },
                })
                .unwrap_or(default);

            // all keys are and'd together to pass the condition, short-circuit early if one doesn't pass
            if !valid {
                return false;
            }
        }
        true
    }};
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
        eval_num_cond!(self, ctx, |condv, ctxv| condv == ctxv)
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
        eval_num_not_cond!(self, ctx, |condv, ctxv| condv == ctxv)
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
        eval_num_cond!(self, ctx, |condv, ctxv| ctxv < condv)
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
        eval_num_cond!(self, ctx, |condv, ctxv| ctxv <= condv)
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
        eval_num_cond!(self, ctx, |condv, ctxv| ctxv > condv)
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
        eval_num_cond!(self, ctx, |condv, ctxv| ctxv >= condv)
    }
}

#[cfg(test)]
mod tests {
    use super::super::*;
    use super::*;
    // required by util::test::eval_test!()
    use util::test::EvalCondTest;

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
        assert_eq!(x, y);
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
        let tests = r#"
        [
            {
                "cond": {
                    "NumericEquals": {
                          "k1": 2,
                          "k2": -7,
                          "k3": "2.02"
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 2,
                            "k2": -7,
                            "k3": "2.02"
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": 2,
                            "k3": "2.02"
                        },
                        "exp": false,
                        "desc": "Missing ctx key; Cond keys are AND'd together"
                    }
                ]
            },
            {
                "cond": {
                    "NumericEquals": {
                          "k1": [5, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": "2.02"
                        },
                        "exp": true,
                        "desc": "Multiple condition values should be OR'd together for a single incoming ctx value"

                    }
                ]
            }
        ]
        "#;

        // normal singular/multiple cond values
        eval_test!(tests);

        let tests = r#"
        [
            {
                "cond": {
                    "IfExists:NumericEquals": {
                          "k1": 2,
                          "k2": -7
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 2,
                            "k2": -7
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k2": -7
                        },
                        "exp": true,
                        "desc": "Should only evaluate if the key is present in the context"
                    },
                    {
                        "ctx": {
                            "k1": 11,
                            "k2": -7
                        },
                        "exp": false
                    }
                ]
            }
        ]
        "#;

        // test IfExists
        eval_test!(tests);

        let tests = r#"
        [
            {
                "cond": {
                    "ForAllValues:NumericEquals": {
                          "k1": [2, -7, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": [2, "2.02"]
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": ["2.02"]
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": -7
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": [2, 11]
                        },
                        "exp": false
                    }
                ]
            }
        ]
        "#;

        // test ForAllValues
        eval_test!(tests);

        let tests = r#"
        [
            {
                "cond": {
                    "ForAnyValue:NumericEquals": {
                          "k1": [2, -7, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 2
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": [11, 15, "2.02"]
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": [-8, 11]
                        },
                        "exp": false
                    }
                ]
            }
        ]
        "#;

        // test ForAnyValue
        eval_test!(tests);
    }

    #[test]
    fn test_eval_numeric_not_equals() {
        let tests = r#"
        [
            {
                "cond": {
                    "NumericNotEquals": {
                          "k1": 2,
                          "k2": -7,
                          "k3": "2.02"
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 3,
                            "k2": -8,
                            "k3": "3.02"
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": 3,
                            "k3": "3.02"
                        },
                        "exp": false,
                        "desc": "Missing ctx key; Cond keys are AND'd together"
                    }
                ]
            },
            {
                "cond": {
                    "NumericNotEquals": {
                          "k1": [5, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": "2.02"
                        },
                        "exp": true,
                        "desc": "Multiple condition values should be OR'd together for a single incoming ctx value"

                    }
                ]
            }
        ]
        "#;

        // normal singular/multiple cond values
        eval_test!(tests);

        let tests = r#"
        [
            {
                "cond": {
                    "IfExists:NumericNotEquals": {
                          "k1": 2,
                          "k2": -7
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 3,
                            "k2": -8
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k2": -8
                        },
                        "exp": true,
                        "desc": "Should only evaluate if the key is present in the context"
                    },
                    {
                        "ctx": {
                            "k1": 11,
                            "k2": -7
                        },
                        "exp": false
                    }
                ]
            }
        ]
        "#;

        // test IfExists
        eval_test!(tests);

        let tests = r#"
        [
            {
                "cond": {
                    "ForAllValues:NumericNotEquals": {
                          "k1": [2, -7, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": [3, "3.02"]
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": ["3.02"]
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": -7
                        },
                        "exp": false
                    }
                ]
            },
            {
                "cond": {
                    "ForAllValues:NumericNotEquals": {
                          "k1": 2
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": [2, "2.02"]
                        },
                        "exp": false
                    },
                    {
                        "ctx": {
                            "k1": [3, "2.02"]
                        },
                        "exp": true
                    }
                ]
            }
        ]
        "#;

        // test ForAllValues
        eval_test!(tests);

        let tests = r#"
        [
            {
                "cond": {
                    "ForAnyValue:NumericNotEquals": {
                          "k1": [2, -7, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 2
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": [11, 15, "2.02"]
                        },
                        "exp": true
                    }
                ]
            },
            {
                "cond": {
                    "ForAnyValue:NumericNotEquals": {
                          "k1": 2
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 2
                        },
                        "exp": false
                    },
                    {
                        "ctx": {
                            "k1": [2, 15]
                        },
                        "exp": true
                    }
                ]
            }
        ]
        "#;

        // test ForAnyValue
        eval_test!(tests);
    }

    #[test]
    fn test_eval_numeric_less_than() {
        let tests = r#"
        [
            {
                "cond": {
                    "NumericLessThan": {
                          "k1": 2,
                          "k2": -7,
                          "k3": "2.02"
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 1,
                            "k2": -8,
                            "k3": "2.01"
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": 1,
                            "k3": "2.01"
                        },
                        "exp": false,
                        "desc": "Missing ctx key; Cond keys are AND'd together"
                    }
                ]
            },
            {
                "cond": {
                    "NumericLessThan": {
                          "k1": [5, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": "2.01"
                        },
                        "exp": true,
                        "desc": "Multiple condition values should be OR'd together for a single incoming ctx value"

                    }
                ]
            }
        ]
        "#;

        // normal singular/multiple cond values
        eval_test!(tests);

        let tests = r#"
        [
            {
                "cond": {
                    "IfExists:NumericLessThan": {
                          "k1": 2,
                          "k2": -7
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 1,
                            "k2": -8
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k2": -8
                        },
                        "exp": true,
                        "desc": "Should only evaluate if the key is present in the context"
                    },
                    {
                        "ctx": {
                            "k1": 2,
                            "k2": -8
                        },
                        "exp": false
                    }
                ]
            }
        ]
        "#;

        // test IfExists
        eval_test!(tests);

        // ForAllValues:NumericLessThan is effectively testing if every request set is < max(cond set)
        let tests = r#"
        [
            {
                "cond": {
                    "ForAllValues:NumericLessThan": {
                          "k1": [2, -7, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": [1, "2.01"]
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": ["2.01", -8]
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": 3
                        },
                        "exp": false
                    },
                    {
                        "ctx": {
                            "k1": [2, "2.02"]
                        },
                        "exp": false
                    }
                ]
            }
        ]
        "#;

        // test ForAllValues
        eval_test!(tests);

        let tests = r#"
        [
            {
                "cond": {
                    "ForAnyValue:NumericLessThan": {
                          "k1": [2, -7, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": "-7.1"
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": [11, 15, "-8.02"]
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": [-7, 11]
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": [3, 11]
                        },
                        "exp": false
                    }
                ]
            }
        ]
        "#;

        // test ForAnyValue
        eval_test!(tests);
    }

    #[test]
    fn test_eval_numeric_less_than_equals() {
        // most of the set operators are tested in NumericLessThan, we just need a sanity check
        // that <= works
        let tests = r#"
        [
            {
                "cond": {
                    "NumericLessThanEquals": {
                          "k1": 2,
                          "k2": -7,
                          "k3": "2.02"
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 1,
                            "k2": -8,
                            "k3": "2.02"
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": 1,
                            "k3": "2.01"
                        },
                        "exp": false,
                        "desc": "Missing ctx key; Cond keys are AND'd together"
                    },
                    {
                        "ctx": {
                            "k1": 1,
                            "k2": -8,
                            "k3": "2.03"
                        },
                        "exp": false
                    }
                ]
            },
            {
                "cond": {
                    "NumericLessThanEquals": {
                          "k1": [5, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": "5"
                        },
                        "exp": true,
                        "desc": "Multiple condition values should be OR'd together for a single incoming ctx value"

                    }
                ]
            }
        ]
        "#;

        eval_test!(tests);
    }

    #[test]
    fn test_eval_numeric_greater_than() {
        let tests = r#"
        [
            {
                "cond": {
                    "NumericGreaterThan": {
                          "k1": 2,
                          "k2": -7,
                          "k3": "2.02"
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 3,
                            "k2": -6,
                            "k3": "2.03"
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": 3,
                            "k3": "2.03"
                        },
                        "exp": false,
                        "desc": "Missing ctx key; Cond keys are AND'd together"
                    },
                    {
                        "ctx": {
                            "k1": 3,
                            "k2": -6,
                            "k3": "2.02"
                        },
                        "exp": false
                    }
                ]
            },
            {
                "cond": {
                    "NumericGreaterThan": {
                          "k1": [5, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": "2.03"
                        },
                        "exp": true,
                        "desc": "Multiple condition values should be OR'd together for a single incoming ctx value"

                    }
                ]
            }
        ]
        "#;

        // normal singular/multiple cond values
        eval_test!(tests);

        let tests = r#"
        [
            {
                "cond": {
                    "IfExists:NumericGreaterThan": {
                          "k1": 2,
                          "k2": -7
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 3,
                            "k2": -6
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k2": -6
                        },
                        "exp": true,
                        "desc": "Should only evaluate if the key is present in the context"
                    },
                    {
                        "ctx": {
                            "k1": 2,
                            "k2": -8
                        },
                        "exp": false
                    }
                ]
            }
        ]
        "#;

        // test IfExists
        eval_test!(tests);

        // ForAllValues:NumericGreaterThan is effectively testing if every request set is > min(cond set)
        let tests = r#"
        [
            {
                "cond": {
                    "ForAllValues:NumericGreaterThan": {
                          "k1": [2, -7, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": [1, "2.02"]
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": -7
                        },
                        "exp": false
                    },
                    {
                        "ctx": {
                            "k1": [-8, 1]
                        },
                        "exp": false
                    }
                ]
            }
        ]
        "#;

        // test ForAllValues
        eval_test!(tests);

        let tests = r#"
        [
            {
                "cond": {
                    "ForAnyValue:NumericGreaterThan": {
                          "k1": [2, -7, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": "-6.9"
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": [-8, -15, "2.03"]
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": [-7, 11]
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": [-7, -8]
                        },
                        "exp": false
                    }
                ]
            }
        ]
        "#;

        // test ForAnyValue
        eval_test!(tests);
    }

    #[test]
    fn test_eval_numeric_greater_than_equals() {
        // most of the set operators are tested in NumericGreaterThan, we just need a sanity check
        // that >= works
        let tests = r#"
        [
            {
                "cond": {
                    "NumericGreaterThanEquals": {
                          "k1": 2,
                          "k2": -7,
                          "k3": "2.02"
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": 3,
                            "k2": -7,
                            "k3": "2.03"
                        },
                        "exp": true
                    },
                    {
                        "ctx": {
                            "k1": 3,
                            "k3": "2.03"
                        },
                        "exp": false,
                        "desc": "Missing ctx key; Cond keys are AND'd together"
                    },
                    {
                        "ctx": {
                            "k1": 3,
                            "k2": -6,
                            "k3": "2.02"
                        },
                        "exp": true
                    }
                ]
            },
            {
                "cond": {
                    "NumericGreaterThanEquals": {
                          "k1": [5, "2.02"]
                    }
                },
                "cases": [
                    {
                        "ctx": {
                            "k1": "2.03"
                        },
                        "exp": true,
                        "desc": "Multiple condition values should be OR'd together for a single incoming ctx value"

                    }
                ]
            }
        ]
        "#;

        // normal singular/multiple cond values
        eval_test!(tests);
    }
}

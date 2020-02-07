use super::condition::{self, Body, EvalModifier, ScalarOrSeq};
use super::Eval;
use crate::wildcard;
use crate::Context;
use serde::{Deserialize, Serialize};
use std::iter::Iterator;

macro_rules! impl_str_cond {
    ($x:ident, $sname:expr) => {
        impl $x {
            /// Create a new condition with initial key/value pair
            pub fn new<S>(key: S, value: S) -> Self
            where
                S: Into<String>,
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
            ///
            /// # Example
            /// NOTE: The example uses `StringEquals` however the method works the same for
            /// all String* condition operators.
            ///
            /// ```
            /// # use riam::conditions::StringEquals;
            /// let mut cond = StringEquals::new("k1", "v1");
            /// cond.add("k1", "v2");
            /// // equivalent JSON:
            /// // {"StringEquals":{"k1": ["v1", "v2"]}}
            /// ```
            pub fn add<'a, S>(&'a mut self, key: S, value: S) -> &'a Self
            where
                S: Into<String>,
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
                    Some(EvalModifier::IfExists) => concat!($sname, ":IfExists"),
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

    ($name:tt) => {
        impl_str_cond!($name, stringify!($name));
    };
}

/// Exact matching, case sensitive
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct StringEquals {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: condition::Body<String>,
}

impl_str_cond!(StringEquals);

// Test whether the context values are a subset of the condition values
fn is_subset<'a, T, F>(cond_values: &[T], ctx_values: &[T], cmp: F) -> bool
where
    F: Fn(&T, &T) -> bool,
{
    'outer: for ctxv in ctx_values.iter() {
        // every value in the context has to be a member of the condition values
        for condv in cond_values.iter() {
            if cmp(condv, ctxv) {
                continue 'outer;
            }
        }

        // no condv matched
        return false;
    }
    true
}

// Test whether any of the context values match at least one of the condition values
fn for_any_match<'a, T, F>(cond_values: &[T], ctx_values: &[T], cmp: F) -> bool
where
    F: Fn(&T, &T) -> bool,
    T: ::std::fmt::Debug,
{
    for ctxv in ctx_values.iter() {
        for condv in cond_values.iter() {
            if cmp(condv, ctxv) {
                return true;
            }
        }
    }
    false
}

// convert a JSON value to a vec handling both scalar and seq types (e.g. "v1" and ["v1", "v2"])
fn serde_json_value_to_vec(v: serde_json::Value) -> Result<Vec<String>, serde_json::Error> {
    let x: ScalarOrSeq<String> = serde_json::from_value(v)?;
    let seq = match x {
        ScalarOrSeq::Scalar(s) => vec![s],
        ScalarOrSeq::Seq(seq) => seq,
    };
    Ok(seq)
}

// fn eval_str_cond<C>(
//     body: &condition::Body<String>,
//     modifier: Option<EvalModifier>,
//     ctx: &Context,
//     cmp: C,
// ) -> bool
// where
//     C: Fn(&str, &str) -> bool,
// {
//     let default = match modifier {
//         Some(EvalModifier::IfExists) => true,
//         _ => false,
//     };
//
//     for (key, values) in body.0.iter() {
//         let valid = ctx
//             .get(key)
//             .and_then(|x| {
//                 match modifier {
//                     Some(EvalModifier::ForAllValues) => {
//                         // all the incoming request context values for the key need to be a subset
//                         // of the condition values
//                         let ctx_values = serde_json_value_to_vec(x.clone())
//                             .ok()
//                             .unwrap_or_else(Vec::new);
//                         Some(is_subset(values, ctx_values.as_slice(), cmp))
//                     }
//                     Some(EvalModifier::ForAnyValue) => {
//                         // at least one of the context values has to match a condition value
//                         let ctx_values = serde_json_value_to_vec(x.clone())
//                             .ok()
//                             .unwrap_or_else(Vec::new);
//                         Some(for_any_match(values, ctx_values.as_slice(), cmp))
//                     }
//                     // possible (cond) value's are OR'd together for evaluation (only 1 needs to pass)
//                     // context is expected to be scalar. If it is a sequence the conditions
//                     // should be using set modifiers
//                     _ => x
//                         .as_str()
//                         .and_then(|v| Some(values.iter().any(|s| cmp(s, v)))),
//                 }
//             })
//             .unwrap_or(default);
//
//         // all keys are and'd together to pass the condition, short-circuit early if one doesn't pass
//         if !valid {
//             return false;
//         }
//     }
//     true
// }

impl Eval for StringEquals {
    fn evaluate(&self, ctx: &Context) -> bool {
        let default = match self.modifier {
            Some(EvalModifier::IfExists) => true,
            _ => false,
        };

        for (key, values) in self.body.0.iter() {
            let valid = ctx
                .get(key)
                .and_then(|x| {
                    match self.modifier {
                        Some(EvalModifier::ForAllValues) => {
                            // all the incoming request context values for the key need to be a subset
                            // of the condition values
                            let ctx_values = serde_json_value_to_vec(x.clone()).ok().unwrap_or_else(Vec::new);
                            Some(is_subset(values, ctx_values.as_slice(), |x, y| x == y))
                        }
                        Some(EvalModifier::ForAnyValue) => {
                            // at least one of the context values has to match a condition value
                            let ctx_values = serde_json_value_to_vec(x.clone()).ok().unwrap_or_else(Vec::new);
                            Some(for_any_match(values, ctx_values.as_slice(), |x, y| x == y))
                        }
                        // possible (cond) value's are OR'd together for evaluation (only 1 needs to pass)
                        // context is expected to be scalar. If it is a sequence the conditions
                        // should be using set modifiers
                        _ => x.as_str().and_then(|v| Some(values.iter().any(|s| s == v))),
                    }
                })
                .unwrap_or(default);

            // all keys are and'd together to pass the condition, short-circuit early if one doesn't pass
            if !valid {
                return false;
            }
        }
        true
    }
}

/// Negated Matching
#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct StringNotEquals {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: condition::Body<String>,
}

impl_str_cond!(StringNotEquals);

impl Eval for StringNotEquals {
    fn evaluate(&self, ctx: &Context) -> bool {
        for (key, values) in self.body.0.iter() {
            let valid = ctx
                .get(key)
                .and_then(|x| x.as_str())
                .and_then(|x| Some(!values.iter().any(|s| s == x)))
                .unwrap_or(false);

            if !valid {
                return false;
            }
        }
        true
    }
}

/// Exact matching, ignoring (value) case.
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct StringEqualsIgnoreCase {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: condition::Body<String>,
}

impl_str_cond!(StringEqualsIgnoreCase);

impl Eval for StringEqualsIgnoreCase {
    fn evaluate(&self, ctx: &Context) -> bool {
        for (key, values) in self.body.0.iter() {
            let valid = ctx
                .get(key)
                .and_then(|x| x.as_str())
                .and_then(|x| Some(x.to_lowercase()))
                .and_then(|x| Some(values.iter().map(|v| v.to_lowercase()).any(|v| v == x)))
                .unwrap_or(false);

            if !valid {
                return false;
            }
        }
        true
    }
}

/// Negated matching, ignoring (value) case.
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct StringNotEqualsIgnoreCase {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: condition::Body<String>,
}

impl_str_cond!(StringNotEqualsIgnoreCase);

impl Eval for StringNotEqualsIgnoreCase {
    fn evaluate(&self, ctx: &Context) -> bool {
        for (key, values) in self.body.0.iter() {
            let valid = ctx
                .get(key)
                .and_then(|x| x.as_str())
                .and_then(|x| Some(x.to_lowercase()))
                .and_then(|x| Some(values.iter().map(|v| v.to_lowercase()).all(|v| v != x)))
                .unwrap_or(false);

            if !valid {
                return false;
            }
        }
        true
    }
}

/// Case-sensitive matching. The values can include a multi-character match wildcard (*) anywhere in the string.
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct StringLike {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: condition::Body<String>,
}

impl_str_cond!(StringLike);

impl Eval for StringLike {
    fn evaluate(&self, ctx: &Context) -> bool {
        for (key, values) in self.body.0.iter() {
            let valid = ctx
                .get(key)
                .and_then(|x| x.as_str())
                .and_then(|x| Some(values.iter().any(|p| wildcard::matches(p, x))))
                .unwrap_or(false);

            if !valid {
                return false;
            }
        }
        true
    }
}

/// Negated case-sensitive matching. The values can include a multi-character match wildcard (*) anywhere in the string.
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct StringNotLike {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: condition::Body<String>,
}

impl_str_cond!(StringNotLike);

impl Eval for StringNotLike {
    fn evaluate(&self, ctx: &Context) -> bool {
        for (key, values) in self.body.0.iter() {
            let valid = ctx
                .get(key)
                .and_then(|x| x.as_str())
                .and_then(|x| Some(values.iter().all(|p| !wildcard::matches(p, x))))
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
        let expected = Condition::StringEquals(StringEquals::new("mykey", "myvalue"));
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
    fn test_string_equals_ignore_case_json() {
        let jsp = r#"
        {
            "StringEqualsIgnoreCase": {
                "mykey": "myvalue"
            }
        }
        "#;

        let actual: Condition = serde_json::from_str(jsp).unwrap();
        let expected = Condition::StringEqualsIgnoreCase(StringEqualsIgnoreCase::new("mykey", "myvalue"));
        assert_eq!(expected, actual);

        let serialized = serde_json::to_string(&expected).unwrap();
        let expected = r#"{"StringEqualsIgnoreCase":{"mykey":"myvalue"}}"#;
        assert_eq!(expected, serialized);
    }

    #[test]
    fn test_string_not_equals_ignore_case_json() {
        let jsp = r#"
        {
            "StringNotEqualsIgnoreCase": {
                "mykey": "myvalue"
            }
        }
        "#;

        let actual: Condition = serde_json::from_str(jsp).unwrap();
        let expected = Condition::StringNotEqualsIgnoreCase(StringNotEqualsIgnoreCase::new("mykey", "myvalue"));
        assert_eq!(expected, actual);

        let serialized = serde_json::to_string(&expected).unwrap();
        let expected = r#"{"StringNotEqualsIgnoreCase":{"mykey":"myvalue"}}"#;
        assert_eq!(expected, serialized);
    }

    #[test]
    fn test_string_like_json() {
        let jsp = r#"
        {
            "StringLike": {
                "mykey": "myvalue"
            }
        }
        "#;

        let actual: Condition = serde_json::from_str(jsp).unwrap();
        let expected = Condition::StringLike(StringLike::new("mykey", "myvalue"));
        assert_eq!(expected, actual);

        let serialized = serde_json::to_string(&expected).unwrap();
        let expected = r#"{"StringLike":{"mykey":"myvalue"}}"#;
        assert_eq!(expected, serialized);
    }

    #[test]
    fn test_string_not_like_json() {
        let jsp = r#"
        {
            "StringNotLike": {
                "mykey": "myvalue"
            }
        }
        "#;

        let actual: Condition = serde_json::from_str(jsp).unwrap();
        let expected = Condition::StringNotLike(StringNotLike::new("mykey", "myvalue"));
        assert_eq!(expected, actual);

        let serialized = serde_json::to_string(&expected).unwrap();
        let expected = r#"{"StringNotLike":{"mykey":"myvalue"}}"#;
        assert_eq!(expected, serialized);
    }

    #[test]
    fn test_eval_string_equals() {
        // singular
        let cond = StringEquals::new("k1", "v1");

        let mut ctx = Context::new();
        ctx.insert("k1", "v1");

        assert!(cond.evaluate(&ctx));

        ctx.insert("k1", "v2");
        assert!(!cond.evaluate(&ctx));

        // multiple allowed
        let mut cond = StringEquals::new("k1", "v1");
        cond.add("k1", "v2");
        assert!(cond.evaluate(&ctx));

        ctx.insert("k1", "v3");
        assert!(!cond.evaluate(&ctx));

        // if exists
        let mut cond = StringEquals::new("kx", "v1");
        cond.with_modifier(EvalModifier::IfExists);
        assert!(cond.evaluate(&ctx), "condition should be true if the key doesn't exist");

        // for all values
        // this condition should only evaluate to true if all values from the incoming context
        // for a particular key belong to the set of values in the cond set
        // i.e. the set(context[key]) is a subset of set(cond[key])
        // cond:
        //   "k1": ["v1", "v2"]
        //
        // context:
        //   "k1": "" // ok (empty set)
        //   "k1": "v1" // ok
        //   "k1": ["v1", "v2"] // ok
        //   "k1": "v3"  // error
        let mut cond = StringEquals::new("k1", "v1");
        cond.add("k1", "v2");
        cond.with_modifier(EvalModifier::ForAllValues);

        let mut ctx = Context::new();
        // FIXME - ensure the empty set is considered a subset
        // assert!(cond.evaluate(&ctx), "the empty set should be a subset");
        ctx.insert("k1", "v1");
        assert!(cond.evaluate(&ctx), "set(v1) should be subset");
        ctx.insert("k1", vec!["v1", "v2"]);
        assert!(cond.evaluate(&ctx), "set(v1, v2) should be subset");
        ctx.insert("k1", "v3");
        assert!(!cond.evaluate(&ctx), "set(v3) should not be subset");
        ctx.insert("k1", vec!["v3", "v1"]);
        assert!(!cond.evaluate(&ctx), "set(v1, v3) should not be subset");

        // for any value
        // cond:
        //   "k1": ["v1", "v2"]
        //
        // context:
        //   "k1": "" // error - empty set doesn't match
        //   "k1": "v1" // ok
        //   "k1": ["v1", "v3"] // ok
        //   "k1": "v3"  // error
        cond.with_modifier(EvalModifier::ForAnyValue);
        let mut ctx = Context::new();
        // FIXME - empty set should NOT be a subset
        // assert!(cond.evaluate(&ctx), "the empty set should NOT be a subset");
        ctx.insert("k1", "v1");
        assert!(cond.evaluate(&ctx), "set(v1) should be subset");
        ctx.insert("k1", vec!["v1", "v2"]);
        assert!(cond.evaluate(&ctx), "set(v1, v2) should be subset");
        // FIXME - finish off test case then figure out how to commonize it (or split into own cases)
        // FIXME - commonize the implementation and add tests for all of the other string condition types
    }

    #[test]
    fn test_eval_string_not_equals() {
        // singular
        let cond = StringNotEquals::new("k1", "v1");
        let mut ctx = Context::new();
        ctx.insert("k1", "v2");
        assert!(cond.evaluate(&ctx));

        ctx.insert("k1", "v1");
        assert!(!cond.evaluate(&ctx));

        // multiple not allowed
        let mut cond = StringNotEquals::new("k1", "v1");
        cond.add("k1", "v2");
        assert!(!cond.evaluate(&ctx));

        ctx.insert("k1", "v3");
        assert!(cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_string_equals_ignore_case() {
        // singular
        let cond = StringEqualsIgnoreCase::new("k1", "value1");

        let mut ctx = Context::new();
        ctx.insert("k1", "VaLue1");

        assert!(cond.evaluate(&ctx));

        ctx.insert("k1", "value2");
        assert!(!cond.evaluate(&ctx));

        // multiple allowed
        let mut cond = StringEqualsIgnoreCase::new("k1", "VaLue1");
        cond.add("k1", "ValUE2");
        assert!(cond.evaluate(&ctx));

        ctx.insert("k1", "v3");
        assert!(!cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_string_not_equals_ignore_case() {
        // singular
        let cond = StringNotEqualsIgnoreCase::new("k1", "value1");

        let mut ctx = Context::new();
        ctx.insert("k1", "VaLue2");

        assert!(cond.evaluate(&ctx));

        ctx.insert("k1", "VaLue1");
        assert!(!cond.evaluate(&ctx));

        // multiple not allowed
        let mut cond = StringNotEqualsIgnoreCase::new("k1", "VaLue1");
        cond.add("k1", "ValUE2");
        assert!(!cond.evaluate(&ctx));

        ctx.insert("k1", "VaLue3");
        assert!(cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_string_like() {
        // singular
        let cond = StringLike::new("k1", "re*123");

        let mut ctx = Context::new();
        ctx.insert("k1", "resources:blog:123");

        assert!(cond.evaluate(&ctx));

        ctx.insert("k1", "resources:blog:456");
        assert!(!cond.evaluate(&ctx));

        // multiple allowed
        let mut cond = StringLike::new("k1", "resources:*:123");
        cond.add("k1", "resources:*:456");
        assert!(cond.evaluate(&ctx));

        ctx.insert("k1", "resources:blog:789");
        assert!(!cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_string_not_like() {
        // singular
        let cond = StringNotLike::new("k1", "re*123");

        let mut ctx = Context::new();
        ctx.insert("k1", "resources:blog:123");

        assert!(!cond.evaluate(&ctx));

        ctx.insert("k1", "resources:blog:456");
        assert!(cond.evaluate(&ctx));

        // multiple not allowed
        let mut cond = StringNotLike::new("k1", "resources:*:123");
        cond.add("k1", "resources:*:456");
        assert!(!cond.evaluate(&ctx));

        ctx.insert("k1", "resources:blog:789");
        assert!(cond.evaluate(&ctx));
    }

    #[test]
    fn test_serialized_name() {
        // same impl across all String* condition types
        let mut cond = StringEquals::new("k1", "v1");
        assert_eq!(cond.serialized_name(), "StringEquals");

        cond.with_modifier(EvalModifier::ForAnyValue);
        assert_eq!(cond.serialized_name(), "ForAnyValue:StringEquals");

        cond.with_modifier(EvalModifier::ForAllValues);
        assert_eq!(cond.serialized_name(), "ForAllValues:StringEquals");

        cond.with_modifier(EvalModifier::IfExists);
        assert_eq!(cond.serialized_name(), "StringEquals:IfExists");
    }

    #[test]
    fn test_string_cond_deserialize_with_eval_modifier() {
        // catch all test for deserialization with modifiers, necessary because of our switch
        // to custom serialization/deserialization logic to enable IAM like syntax of serialized policies
        let jsp = r#"
        [
            {"ForAnyValue:StringEquals": {"k": "v"}},
            {"ForAllValues:StringEquals": {"k": "v"}},
            {"IfExists:StringEquals": {"k": "v"}},
            {"ForAnyValue:StringNotEquals": {"k": "v"}},
            {"ForAllValues:StringNotEquals": {"k": "v"}},
            {"IfExists:StringNotEquals": {"k": "v"}},
            {"ForAnyValue:StringEqualsIgnoreCase": {"k": "v"}},
            {"ForAllValues:StringEqualsIgnoreCase": {"k": "v"}},
            {"IfExists:StringEqualsIgnoreCase": {"k": "v"}},
            {"ForAnyValue:StringNotEqualsIgnoreCase": {"k": "v"}},
            {"ForAllValues:StringNotEqualsIgnoreCase": {"k": "v"}},
            {"IfExists:StringNotEqualsIgnoreCase": {"k": "v"}},
            {"ForAnyValue:StringLike": {"k": "v"}},
            {"ForAllValues:StringLike": {"k": "v"}},
            {"IfExists:StringLike": {"k": "v"}},
            {"ForAnyValue:StringNotLike": {"k": "v"}},
            {"ForAllValues:StringNotLike": {"k": "v"}},
            {"IfExists:StringNotLike": {"k": "v"}}
        ]
        "#;

        // create a condition with an eval modifier set for this test
        macro_rules! new_cond {
            ( $t:ident, $modifier:ident) => {{
                let mut c = $t::new("k", "v");
                c.with_modifier(EvalModifier::$modifier);
                Condition::$t(c)
            }};
        }

        let actual: Vec<Condition> = serde_json::from_str(jsp).unwrap();
        let expected = vec![
            new_cond!(StringEquals, ForAnyValue),
            new_cond!(StringEquals, ForAllValues),
            new_cond!(StringEquals, IfExists),
            new_cond!(StringNotEquals, ForAnyValue),
            new_cond!(StringNotEquals, ForAllValues),
            new_cond!(StringNotEquals, IfExists),
            new_cond!(StringEqualsIgnoreCase, ForAnyValue),
            new_cond!(StringEqualsIgnoreCase, ForAllValues),
            new_cond!(StringEqualsIgnoreCase, IfExists),
            new_cond!(StringNotEqualsIgnoreCase, ForAnyValue),
            new_cond!(StringNotEqualsIgnoreCase, ForAllValues),
            new_cond!(StringNotEqualsIgnoreCase, IfExists),
            new_cond!(StringLike, ForAnyValue),
            new_cond!(StringLike, ForAllValues),
            new_cond!(StringLike, IfExists),
            new_cond!(StringNotLike, ForAnyValue),
            new_cond!(StringNotLike, ForAllValues),
            new_cond!(StringNotLike, IfExists),
        ];
        assert_eq!(expected, actual);
    }
}

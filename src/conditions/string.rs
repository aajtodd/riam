use super::condition::{self, Body, EvalModifier, ScalarOrSeq};
use super::{util, Eval};
use crate::wildcard;
use crate::Context;
use serde::{Deserialize, Serialize};
use std::iter::Iterator;

// convert a JSON value to a vec handling both scalar and seq types (e.g. "v1" and ["v1", "v2"])
fn serde_json_value_to_vec(v: serde_json::Value) -> Result<Vec<String>, serde_json::Error> {
    let x: ScalarOrSeq<String> = serde_json::from_value(v)?;
    let seq = match x {
        ScalarOrSeq::Scalar(s) => vec![s],
        ScalarOrSeq::Seq(seq) => seq,
    };
    Ok(seq)
}

macro_rules! eval_str_cond {
    ($cond:ident, $ctx:ident, $cmp:expr) => {{
        // use the same comparison lambda for both forall/forany as well as the singular case
        eval_str_cond!($cond, $ctx, $cmp, $cmp)
    }};

    // condition, context, lambda used for comparison (plural), lambda used for comparison (singular)
    // ... why the distinction you ask. Well the signatures of for_any_match, is_subset, etc do not
    // match the signature of the singular case (&String vs &str). I'm sure there is a way around
    // this but I haven't seen a clean way that keeps the functions generic over any type T without
    // be more specific and specifying &str (which would fix the ambiguity and difference between
    // the two cases). For now allow the closures to be specified independently *if needed*.
    ($cond:ident, $ctx:ident, $cmp:expr, $scmp:expr) => {{
        let default = match $cond.modifier {
            Some(EvalModifier::IfExists) => true,
            _ => false,
        };

        for (key, values) in $cond.body.0.iter() {
            let valid = $ctx
                .get(key)
                .and_then(|x| {
                    match $cond.modifier {
                        Some(EvalModifier::ForAllValues) => {
                            // all the incoming request context values for the key need to be a subset
                            // of the condition values
                            let ctx_values = serde_json_value_to_vec(x.clone()).ok().unwrap_or_else(Vec::new);
                            Some(util::is_subset(values, ctx_values.as_slice(), $cmp))
                        }
                        Some(EvalModifier::ForAnyValue) => {
                            // at least one of the context values has to match a condition value
                            let ctx_values = serde_json_value_to_vec(x.clone()).ok().unwrap_or_else(Vec::new);
                            Some(util::intersects(values, ctx_values.as_slice(), $cmp))
                        }
                        // possible (cond) value's are OR'd together for evaluation (only 1 needs to pass)
                        // context is expected to be scalar. If it is a sequence the conditions
                        // should be using set modifiers
                        _ => x
                            .as_str()
                            .and_then(|v| Some(values.iter().any(|s| $scmp(s, v))))
                            // it is important that if as_str() returns None that we don't use the
                            // default. It should be false no matter what if the conversion fails
                            // as we are expecting a string here AND the key did exist. This mostly
                            // affects IfExists where the default is true
                            .or(Some(false)),
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

macro_rules! eval_str_not_cond {
    ($cond:ident, $ctx:ident, $cmp:expr) => {{
        // use the same comparison lambda for both forall/forany as well as the singular case
        eval_str_not_cond!($cond, $ctx, $cmp, $cmp)
    }};
    // condition, context, lambda used for comparison (the lambda be the equals case. The inversion
    // is handled internally to the macro, e.g. |x,y| x == y should be used instead of |x,y| x !=
    // y). This is to handle the different modifier cases.
    // NOTE: See the comments on eval_str_cond!() for why scmp ugliness is part of the equation
    ($cond:ident, $ctx:ident, $cmp:expr, $scmp:expr) => {{
        let default = match $cond.modifier {
            Some(EvalModifier::IfExists) => true,
            _ => false,
        };

        for (key, values) in $cond.body.0.iter() {
            let valid = $ctx
                .get(key)
                .and_then(|x| {
                    match $cond.modifier {
                        Some(EvalModifier::ForAllValues) => {
                            // all the incoming request context values for the key need to NOT
                            // match any of the condition values (i.e. they do not intersect)
                            let ctx_values = serde_json_value_to_vec(x.clone()).ok().unwrap_or_else(Vec::new);
                            Some(util::is_disjoint(values, ctx_values.as_slice(), $cmp))
                        }
                        Some(EvalModifier::ForAnyValue) => {
                            // at least one of the context values has to _not_ match a condition value (hence the inversion)
                            let ctx_values = serde_json_value_to_vec(x.clone()).ok().unwrap_or_else(Vec::new);
                            Some(util::intersects(values, ctx_values.as_slice(), |x, y| !($cmp(x, y))))
                        }
                        // possible (cond) value's are OR'd together for evaluation (only 1 needs to pass)
                        // context is expected to be scalar. If it is a sequence the conditions
                        // should be using set modifiers
                        _ => x
                            .as_str()
                            .and_then(|v| Some(!values.iter().any(|s| $scmp(s, v))))
                            // it is important that if as_str() returns None that we don't use the
                            // default. It should be false no matter what if the conversion fails
                            // as we are expecting a string here AND the key did exist. This mostly
                            // affects IfExists where the default is true
                            .or(Some(false)),
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

/// Exact matching, case sensitive
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct StringEquals {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: condition::Body<String>,
}

impl_cond_base!(StringEquals, String);

impl Eval for StringEquals {
    fn evaluate(&self, ctx: &Context) -> bool {
        eval_str_cond!(self, ctx, |x, y| x == y)
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

impl_cond_base!(StringNotEquals, String);

impl Eval for StringNotEquals {
    fn evaluate(&self, ctx: &Context) -> bool {
        eval_str_not_cond!(self, ctx, |x, y| x == y)
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

impl_cond_base!(StringEqualsIgnoreCase, String);

impl Eval for StringEqualsIgnoreCase {
    fn evaluate(&self, ctx: &Context) -> bool {
        eval_str_cond!(
            self,
            ctx,
            |x: &String, y: &String| x.to_lowercase() == y.to_lowercase(),
            // the singular case has a different signature, ugly hack for now
            |x: &str, y: &str| x.to_lowercase() == y.to_lowercase()
        )
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

impl_cond_base!(StringNotEqualsIgnoreCase, String);

impl Eval for StringNotEqualsIgnoreCase {
    fn evaluate(&self, ctx: &Context) -> bool {
        eval_str_not_cond!(
            self,
            ctx,
            |x: &String, y: &String| x.to_lowercase() == y.to_lowercase(),
            // the singular case has a different signature, ugly hack for now
            |x: &str, y: &str| x.to_lowercase() == y.to_lowercase()
        )
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

impl_cond_base!(StringLike, String);

impl Eval for StringLike {
    fn evaluate(&self, ctx: &Context) -> bool {
        eval_str_cond!(self, ctx, |p, y| wildcard::matches(p, y))
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

impl_cond_base!(StringNotLike, String);

impl Eval for StringNotLike {
    fn evaluate(&self, ctx: &Context) -> bool {
        eval_str_not_cond!(self, ctx, |p, y| wildcard::matches(p, y))
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

    use serde_json::Value;
    #[derive(Deserialize, Debug)]
    struct EvalModifierTestCase {
        context: HashMap<String, Value>,
        expected: bool,
        desc: String,
    }

    macro_rules! eval_test_cases {
        ( $cond:ident, $test_js:ident) => {
            let tests: Vec<EvalModifierTestCase> = serde_json::from_str($test_js).unwrap();
            for t in tests {
                let mut ctx = Context::new();
                for (key, values) in t.context {
                    ctx.insert(key.clone(), values);
                }

                let actual = $cond.evaluate(&ctx);
                assert_eq!(
                    t.expected, actual,
                    "context: {:?}\ncond: {:?}\n{} ",
                    &ctx, $cond, t.desc
                );
            }
        };
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
        cond.push("k1", "v2");
        assert!(cond.evaluate(&ctx));

        ctx.insert("k1", "v3");
        assert!(!cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_if_exists_string_equals() {
        // if exists
        let mut cond = StringEquals::new("kx", "v1");
        cond.with_modifier(EvalModifier::IfExists);

        // NOTE: Be careful of context values be singular string vs array of strings because
        // evaluation uses as_str() when there isn't a set modifier
        let cases = r#"
        [
            {"context": {}, "expected": true, "desc": "condition should be true if the key doesn't exist"},
            {"context": {"kx": "v1"}, "expected": true, "desc": "condition should be true if the key matches"},
            {"context": {"kx": "vn"}, "expected": false, "desc": "cond should not be true if key does not match"},
            {"context": {"kx": ["v1"]}, "expected": false, "desc": "special case, cond requires set modifier for proper evaluation"}
        ]
        "#;
        // The last case is a special case where the incoming context is expected to be singular. A
        // context with multiple values for a single key requires set modifiers on the condition, IfExists can't be used for this.
        // e.g.
        // Cond(k1: v1) == {k1: [v1]}
        //     OR
        // Cond(k1: [v1, v2])  == {k1: [v1, v2]}
        eval_test_cases!(cond, cases);
    }

    #[test]
    fn test_eval_for_all_values_string_equals() {
        // for all values
        // this condition should only evaluate to true if all values from the incoming context
        // for a particular key belong to the set of values in the cond set
        // i.e. the set(context[key]) is a subset of set(cond[key])
        // cond:
        //   "k1": ["v1", "v2"]
        //
        // context:
        //   "k1": "v1" // ok
        //   "k1": ["v1", "v2"] // ok
        //   "k1": "v3"  // error
        //   "k1": ["v1", "v3"]  // error
        let mut cond = StringEquals::new("k1", "v1");
        cond.push("k1", "v2");
        cond.with_modifier(EvalModifier::ForAllValues);

        // FIXME - empty set should be considered a subset
        let cases = r#"
        [
            {"context": {"k1": ["v1"]}, "expected": true, "desc": "set(v1) should be a subset"},
            {"context": {"k1": ["v1", "v2"]}, "expected": true, "desc": "set(v1, v2) should be a subset"},
            {"context": {"k1": ["v3"]}, "expected": false, "desc": "set(v3) should not be a subset"},
            {"context": {"k1": ["v1", "v3"]}, "expected": false, "desc": "set(v1, v3) should not be a subset"}
        ]
        "#;
        eval_test_cases!(cond, cases);
    }

    #[test]
    fn test_eval_for_any_value_string_equals() {
        // for any value
        // cond:
        //   "k1": ["v1", "v2"]
        //
        // context:
        //   "k1": "" // error - empty set doesn't match
        //   "k1": "v1" // ok
        //   "k1": ["v1", "v3"] // ok
        //   "k1": "v3"  // error
        //   "k1": ["v3", "v4"]  // error
        let mut cond = StringEquals::new("k1", "v1");
        cond.with_modifier(EvalModifier::ForAnyValue);
        // FIXME - empty set should be considered a subset
        let cases = r#"
        [
            {"context": {"k1": ["v1"]}, "expected": true, "desc": "set(v1) should intersect"},
            {"context": {"k1": ["v1", "v3"]}, "expected": true, "desc": "set(v1, v3) should intersect"},
            {"context": {"k1": ["v3"]}, "expected": false, "desc": "set(v3) should be disjoint"},
            {"context": {"k1": ["v3", "v4"]}, "expected": false, "desc": "set(v3, v4) should be disjoint"}
        ]
        "#;
        eval_test_cases!(cond, cases);
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

        // multiple
        let mut cond = StringNotEquals::new("k1", "v1");
        cond.push("k1", "v2");
        assert!(!cond.evaluate(&ctx));

        ctx.insert("k1", "v3");
        assert!(cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_if_exists_string_not_equals() {
        // if exists
        let mut cond = StringNotEquals::new("kx", "v1");
        cond.with_modifier(EvalModifier::IfExists);

        let cases = r#"
        [
            {"context": {}, "expected": true, "desc": "condition should be true if the key doesn't exist"},
            {"context": {"kx": "v1"}, "expected": false, "desc": "condition should be false if the key matches"},
            {"context": {"kx": "vn"}, "expected": true, "desc": "cond should be true if key does not match"},
            {"context": {"kx": ["vn"]}, "expected": false, "desc": "special case, cond requires set modifier for proper evaluation"}
        ]
        "#;
        eval_test_cases!(cond, cases);
    }

    #[test]
    fn test_eval_for_all_values_string_not_equals() {
        // for all values
        // this condition should only evaluate to true if all values from the incoming context
        // for a particular key do not belong to the set of values in the cond set
        // i.e. the set(context[key]) is not a subset of set(cond[key])
        // cond:
        //   "k1": ["v1", "v2"]
        //
        // context:
        //   "k1": "" // ok (empty set)
        //   "k1": "v3" // ok
        //   "k1": ["v3", "v4"] // ok
        //   "k1": "v1"  // error
        //   "k1": ["v1", "v2"]  // error
        //   "k1": ["v3", "v2"]  // error
        let mut cond = StringNotEquals::new("k1", "v1");
        cond.push("k1", "v2");
        cond.with_modifier(EvalModifier::ForAllValues);

        let cases = r#"
        [
            {"context": {"k1": ["v3"]}, "expected": true, "desc": "set(v3) should be disjoint"},
            {"context": {"k1": ["v3", "v4"]}, "expected": true, "desc": "set(v3, v4) should be disjoint"},
            {"context": {"k1": "v1"}, "expected": false, "desc": "set(v1) should intersect"},
            {"context": {"k1": ["v1", "v2"]}, "expected": false, "desc": "set(v1, v2) should intersect"},
            {"context": {"k1": ["v3", "v2"]}, "expected": false, "desc": "set(v3, v2) should intersect"}
        ]
        "#;
        eval_test_cases!(cond, cases);
    }

    #[test]
    fn test_eval_for_any_value_string_not_equals() {
        // for any value
        // cond:
        //   "k1": ["v1", "v2"]
        //
        // context:
        //   "k1": "" // error - empty set doesn't match
        //   "k1": "v3" // ok
        //   "k1": ["v1", "v3"] // ok
        //   "k1": "v1"  // ok (v1 doesn't match cond value v2)
        let mut cond = StringNotEquals::new("k1", "v1");
        cond.push("k1", "v2");
        cond.with_modifier(EvalModifier::ForAnyValue);

        let cases = r#"
        [
            {"context": {"k1": ["v3"]}, "expected": true, "desc": "set(v3) should be disjoint"},
            {"context": {"k1": ["v1", "v3"]}, "expected": true, "desc": "v3 should not match v1/v2"},
            {"context": {"k1": "v1"}, "expected": true, "desc": "v1 should not match v2"}
        ]
        "#;
        eval_test_cases!(cond, cases);

        // the last two cases are odd, since the cond specifies two possible values, any value
        // will work because the incoming value will ultimately not match one of the cond values
        // In other words don't use it like this...
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
        cond.push("k1", "ValUE2");
        assert!(cond.evaluate(&ctx));

        ctx.insert("k1", "v3");
        assert!(!cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_if_exists_string_equals_ignore_case() {
        // if exists
        let mut cond = StringEqualsIgnoreCase::new("kx", "VaLue1");
        cond.with_modifier(EvalModifier::IfExists);

        let cases = r#"
        [
            {"context": {}, "expected": true, "desc": "condition should be true if the key doesn't exist"},
            {"context": {"kx": "vALue1"}, "expected": true, "desc": "condition should be true if the key matches"},
            {"context": {"kx": "value2"}, "expected": false, "desc": "cond should not be true if key does not match"},
            {"context": {"kx": ["vALue1"]}, "expected": false, "desc": "special case, cond requires set modifier for proper evaluation"}
        ]
        "#;
        eval_test_cases!(cond, cases);
    }

    #[test]
    fn test_eval_for_all_values_string_equals_ignore_case() {
        let mut cond = StringEqualsIgnoreCase::new("k1", "VaLue1");
        cond.push("k1", "VALue2");
        cond.with_modifier(EvalModifier::ForAllValues);

        let cases = r#"
        [
            {"context": {"k1": ["VALUE1"]}, "expected": true, "desc": "set(VALUE1) should be a subset"},
            {"context": {"k1": ["value1", "VALUE2"]}, "expected": true, "desc": "set(v1, v2) should be a subset"},
            {"context": {"k1": ["v3"]}, "expected": false, "desc": "set(v3) should not be a subset"},
            {"context": {"k1": ["vALue1", "v3"]}, "expected": false, "desc": "set(v1, v3) should not be a subset"}
        ]
        "#;
        eval_test_cases!(cond, cases);
    }

    #[test]
    fn test_eval_for_any_value_string_equals_ignore_case() {
        let mut cond = StringEqualsIgnoreCase::new("k1", "VaLue1");
        cond.with_modifier(EvalModifier::ForAnyValue);
        let cases = r#"
        [
            {"context": {"k1": ["value1"]}, "expected": true, "desc": "set(v1) should intersect"},
            {"context": {"k1": ["VALue1", "v3"]}, "expected": true, "desc": "set(v1, v3) should intersect"},
            {"context": {"k1": ["v3"]}, "expected": false, "desc": "set(v3) should be disjoint"},
            {"context": {"k1": ["v3", "v4"]}, "expected": false, "desc": "set(v3, v4) should be disjoint"}
        ]
        "#;
        eval_test_cases!(cond, cases);
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
        cond.push("k1", "ValUE2");
        assert!(!cond.evaluate(&ctx));

        ctx.insert("k1", "VaLue3");
        assert!(cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_if_exists_string_not_equals_ignore_case() {
        let mut cond = StringNotEqualsIgnoreCase::new("kx", "VaLue1");
        cond.with_modifier(EvalModifier::IfExists);

        let cases = r#"
        [
            {"context": {}, "expected": true, "desc": "condition should be true if the key doesn't exist"},
            {"context": {"kx": "vALue2"}, "expected": true, "desc": "condition should be true if the key does not match"},
            {"context": {"kx": "value1"}, "expected": false, "desc": "cond should not be true if key matches"},
            {"context": {"kx": ["vALue2"]}, "expected": false, "desc": "special case, cond requires set modifier for proper evaluation"}
        ]
        "#;
        eval_test_cases!(cond, cases);
    }

    #[test]
    fn test_eval_for_all_values_string_not_equals_ignore_case() {
        let mut cond = StringNotEqualsIgnoreCase::new("k1", "VaLue1");
        cond.push("k1", "VALue2");
        cond.with_modifier(EvalModifier::ForAllValues);

        let cases = r#"
        [
            {"context": {"k1": ["VALUE1"]}, "expected": false, "desc": "set(VALUE1) intersects"},
            {"context": {"k1": ["value1", "VALUE2"]}, "expected": false, "desc": "set(v1, v2) intersects"},
            {"context": {"k1": ["v3"]}, "expected": true, "desc": "set(v3) should be disjoint"},
            {"context": {"k1": ["vALue3", "v4"]}, "expected": true, "desc": "set(v3, v4) should be disjoint"},
            {"context": {"k1": ["v3", "vALuE2"]}, "expected": false, "desc": "set(v3, vALuE2) should intersect"}
        ]
        "#;
        eval_test_cases!(cond, cases);
    }

    #[test]
    fn test_eval_for_any_value_string_not_equals_ignore_case() {
        let mut cond = StringNotEqualsIgnoreCase::new("k1", "VaLue1");
        cond.with_modifier(EvalModifier::ForAnyValue);
        let cases = r#"
        [
            {"context": {"k1": ["value1"]}, "expected": false, "desc": "set(v1) should intersect"},
            {"context": {"k1": ["VALue1", "v3"]}, "expected": true, "desc": "set(value1, v3), v3 should not match"},
            {"context": {"k1": ["v3"]}, "expected": true, "desc": "set(v3) should be disjoint"},
            {"context": {"k1": ["v3", "v4"]}, "expected": true, "desc": "set(v3, v4) should be disjoint"}
        ]
        "#;
        eval_test_cases!(cond, cases);
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
        cond.push("k1", "resources:*:456");
        assert!(cond.evaluate(&ctx));

        ctx.insert("k1", "resources:blog:789");
        assert!(!cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_if_exists_string_like() {
        // if exists
        let mut cond = StringLike::new("kx", "re*123");
        cond.with_modifier(EvalModifier::IfExists);

        let cases = r#"
        [
            {"context": {}, "expected": true, "desc": "condition should be true if the key doesn't exist"},
            {"context": {"kx": "resources:blog:123"}, "expected": true, "desc": "condition should be true if the key matches"},
            {"context": {"kx": "resources:blog:456"}, "expected": false, "desc": "cond should not be true if key does not match"},
            {"context": {"kx": ["resources:blog:123"]}, "expected": false, "desc": "special case, cond requires set modifier for proper evaluation"}
        ]
        "#;
        eval_test_cases!(cond, cases);
    }

    #[test]
    fn test_eval_for_all_values_string_like() {
        let mut cond = StringLike::new("k1", "re*123");
        cond.push("k1", "actions:create:*");
        cond.with_modifier(EvalModifier::ForAllValues);

        let cases = r#"
        [
            {"context": {"k1": ["resources:blog:123"]}, "expected": true, "desc": "set(resources:blog:123) should be a subset"},
            {"context": {"k1": ["resources:account:123", "actions:create:account"]}, "expected": true, "desc": "values should be a subset"},
            {"context": {"k1": ["resources:blog:125"]}, "expected": false, "desc": "values should not be a subset"},
            {"context": {"k1": ["resources:blog:123", "actions:delete:123"]}, "expected": false, "desc": "values should not be a subset"}
        ]
        "#;
        eval_test_cases!(cond, cases);
    }

    #[test]
    fn test_eval_for_any_value_string_like() {
        let mut cond = StringLike::new("k1", "re*123");
        cond.push("k1", "actions:create:*");
        cond.with_modifier(EvalModifier::ForAnyValue);
        let cases = r#"
        [
            {"context": {"k1": ["resources:blog:123"]}, "expected": true, "desc": "set(resources:blog:123) should intersect"},
            {"context": {"k1": ["resources:account:456", "actions:create:account"]}, "expected": true, "desc": "values should intersect"},
            {"context": {"k1": ["resources:blog:125"]}, "expected": false, "desc": "values should not intersect"},
            {"context": {"k1": ["resources:blog:456", "actions:delete:123"]}, "expected": false, "desc": "values should not intersect"}
        ]
        "#;
        eval_test_cases!(cond, cases);
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
        cond.push("k1", "resources:*:456");
        assert!(!cond.evaluate(&ctx));

        ctx.insert("k1", "resources:blog:789");
        assert!(cond.evaluate(&ctx));
    }

    #[test]
    fn test_eval_if_exists_string_not_like() {
        // if exists
        let mut cond = StringNotLike::new("kx", "re*123");
        cond.with_modifier(EvalModifier::IfExists);

        let cases = r#"
        [
            {"context": {}, "expected": true, "desc": "condition should be true if the key doesn't exist"},
            {"context": {"kx": "resources:blog:123"}, "expected": false, "desc": "condition should be false if the key matches"},
            {"context": {"kx": "resources:blog:456"}, "expected": true, "desc": "cond should be true if key does not match"},
            {"context": {"kx": ["resources:blog:456"]}, "expected": false, "desc": "special case, cond requires set modifier for proper evaluation"}
        ]
        "#;
        eval_test_cases!(cond, cases);
    }

    #[test]
    fn test_eval_for_all_values_string_not_like() {
        let mut cond = StringNotLike::new("k1", "re*123");
        cond.push("k1", "actions:create:*");
        cond.with_modifier(EvalModifier::ForAllValues);

        let cases = r#"
        [
            {"context": {"k1": ["resources:blog:123"]}, "expected": false, "desc": "set(resources:blog:123) should intersect"},
            {"context": {"k1": ["resources:account:456", "actions:delete:account"]}, "expected": true, "desc": "values should not intersect"},
            {"context": {"k1": ["resources:blog:125"]}, "expected": true, "desc": "values should not intersect"},
            {"context": {"k1": ["resources:blog:456", "actions:create:account"]}, "expected": false, "desc": "values should intersect"}
        ]
        "#;
        eval_test_cases!(cond, cases);
    }

    #[test]
    fn test_eval_for_any_value_string_not_like() {
        let mut cond = StringNotLike::new("k1", "re*123");
        cond.with_modifier(EvalModifier::ForAnyValue);
        let cases = r#"
        [
            {"context": {"k1": ["resources:blog:123"]}, "expected": false, "desc": "set(resources:blog:123) should intersect"},
            {"context": {"k1": ["resources:account:456", "actions:create:account"]}, "expected": true, "desc": "values should not intersect"},
            {"context": {"k1": ["resources:blog:125"]}, "expected": true, "desc": "values should not intersect"},
            {"context": {"k1": ["resources:blog:123", "actions:delete:123"]}, "expected": true, "desc": "action should not match"}
        ]
        "#;
        eval_test_cases!(cond, cases);
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
        assert_eq!(cond.serialized_name(), "IfExists:StringEquals");
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

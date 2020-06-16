// TODO - rename body::insert to body::push. Add an insert() method that does a replace inplace
// like HashMap::insert
/// Implement common condition functions. This macro works with all condition types that look like:
///
/// struct Cond{modifier: Option<EvalModifier>, body: Body<T>}
///
/// Which is to say all conditions that accept eval modifiers and support multiple values for a
/// condition key.
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

/// Test whether the context values are a subset of the condition values.
/// The comparison function F will be invoked as F(condv, ctxv)
pub fn is_subset<'a, T, F>(cond_values: &[T], ctx_values: &[T], cmp: F) -> bool
where
    F: Fn(&T, &T) -> bool,
    T: ::std::fmt::Debug,
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

/// Test whether there is an intersection between the context values and the condition values
/// The comparison function F will be invoked as F(condv, ctxv)
pub fn intersects<'a, T, F>(cond_values: &[T], ctx_values: &[T], cmp: F) -> bool
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

/// test whether all of the context values are not equal to any of the condition values, equivalent
/// to testing for the empty intersection.
/// The comparison function F will be invoked as F(condv, ctxv)
pub fn is_disjoint<T, F>(cond_values: &[T], ctx_values: &[T], cmp: F) -> bool
where
    F: Fn(&T, &T) -> bool,
    T: ::std::fmt::Debug,
{
    !intersects(cond_values, ctx_values, cmp)
}

#[cfg(test)]
#[macro_use]
pub mod test {
    use crate::conditions::Condition;
    use crate::Context;
    use serde::{Deserialize, Serialize};

    /// Implements to and from JSON test for a condition. Invoked as `json_test!(CondType)`
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

    #[derive(Serialize, Deserialize, Debug)]
    pub struct EvalTestCase {
        // the context to evaluate
        pub ctx: Context,

        // expected value when this context is evaluated against the given test condition
        pub exp: bool,

        // description of this test case
        #[serde(default)]
        pub desc: String,
    }

    #[derive(Serialize, Deserialize, Debug)]
    pub struct EvalCondTest {
        // condition to evaluate
        pub cond: Condition,
        // cases to evaluate against this single condition
        pub cases: Vec<EvalTestCase>,
    }

    /// Run a set of test cases testing evaluate for a condition. The macro is invoked
    /// as `eval_test(cases)` where cases is JSON structured like:
    ///
    /// ```
    /// let tests = r#"
    /// [
    ///     {
    ///         "cond": {
    ///             "NumericEquals": {
    ///                   "k1": 2
    ///             }
    ///         },
    ///         "cases": [
    ///             {
    ///                 "ctx": {
    ///                     "k1": 2
    ///                 },
    ///                 "exp": true
    ///             }
    ///         ]
    ///     }
    /// ]"#;
    /// ```
    /// Where each entry is a condition and a set of contexts to evaluate against that condition.
    ///
    macro_rules! eval_test {
        ($cases:ident) => {
            let tests: Vec<EvalCondTest> = serde_json::from_str($cases).unwrap();
            for (i, test) in tests.iter().enumerate() {
                for (j, case) in test.cases.iter().enumerate() {
                    let actual = test.cond.evaluate(&case.ctx);
                    assert_eq!(
                        case.exp, actual,
                        "test {} case {} failed; cond: {:?}; ctx: {:?}; desc: {}",
                        i, j, test.cond, case.ctx, case.desc
                    );
                }
            }
        };
    }
}

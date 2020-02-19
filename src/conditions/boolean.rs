use super::Eval;
use crate::Context;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Boolean conditions compare an incoming request key to `true` or `false`
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct Bool {
    #[serde(skip)]
    if_exists: bool,

    // special case - bool cond does not allow multiple values per key
    #[serde(flatten)]
    body: HashMap<String, bool>,
}

impl Bool {
    /// Create a new condition with initial key/value pair
    pub fn new<K, V>(key: K, value: V) -> Self
    where
        K: Into<String>,
        V: Into<bool>,
    {
        let mut m = HashMap::new();
        m.insert(key.into(), value.into());
        Bool {
            if_exists: false,
            body: m,
        }
    }

    /// Insert a key into the condition with the expected value. If the key did not exist
    /// it inserts a new one, if it did the value is updated in-place.
    pub fn insert<K, V>(&mut self, key: K, value: V)
    where
        K: Into<String>,
        V: Into<bool>,
    {
        self.body.insert(key.into(), value.into());
    }

    /// Set the "IfExists" modifier for this condition
    pub fn set_if_exists(&mut self) {
        self.if_exists = true;
    }

    /// The name that should be used to serialize this condition.
    /// Modifiers IfExists can change the expected serialized name.
    pub(crate) fn serialized_name(&self) -> &'static str {
        match self.if_exists {
            true => "IfExists:Bool",
            false => "Bool",
        }
    }
}

impl Eval for Bool {
    fn evaluate(&self, ctx: &Context) -> bool {
        for (key, value) in self.body.iter() {
            let valid = ctx
                .get(key)
                .and_then(|x| x.as_bool())
                .and_then(|x| Some(x == *value))
                .unwrap_or(self.if_exists);

            // all keys are and'd together to pass the condition, short-circuit early if one doesn't pass
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
            "Bool": {
                "mykey": true
            }
        }
        "#;

        let actual: Condition = serde_json::from_str(jsp).unwrap();
        let expected = Condition::Bool(Bool::new("mykey", true));
        assert_eq!(expected, actual);

        let serialized = serde_json::to_string(&expected).unwrap();
        let expected = r#"{"Bool":{"mykey":true}}"#;
        assert_eq!(expected, serialized);

        // if exists
        let jsp = r#"
        {
            "IfExists:Bool": {
                "mykey": false 
            }
        }
        "#;

        let actual: Condition = serde_json::from_str(jsp).unwrap();
        let mut c = Bool::new("mykey", false);
        c.set_if_exists();

        let expected = Condition::Bool(c);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_eval_bool() {
        let mut cond = Bool::new("k1", true);
        cond.insert("k2", false);

        let mut ctx = Context::new();
        ctx.insert("k1", true);
        ctx.insert("k2", false);

        assert!(cond.evaluate(&ctx));

        ctx.insert("k1", false);
        assert!(!cond.evaluate(&ctx));
    }

    #[test]
    fn test_serialized_name() {
        let mut cond = Bool::new("k1", true);
        assert_eq!(cond.serialized_name(), "Bool");

        cond.set_if_exists();
        assert_eq!(cond.serialized_name(), "IfExists:Bool");
    }
}

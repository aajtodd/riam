use serde::{Deserialize, Serialize};

/// Effect indicates whether a policy statement allows or denies access
#[derive(Serialize, Deserialize, Eq, PartialEq, Debug)]
pub enum Effect {
    #[serde(rename = "allow")]
    Allow,
    #[serde(rename = "deny")]
    Deny,
}

/// Statement contains information about a single permission
#[derive(Serialize, Deserialize, PartialEq, Debug)]
pub struct Statement {
    effect: Effect,
    actions: Vec<String>,
    resources: Vec<String>,
}

/// Policy represents an access control policy which is used to either grant or deny a
/// principal (users/groups/roles/etc) actions on specific resources.
#[derive(Serialize, Deserialize, PartialEq, Debug)]
pub struct Policy {
    #[serde(skip_serializing_if = "Option::is_none")]
    sid: Option<String>,
    principals: Vec<String>,
    statements: Vec<Statement>,
}

impl Policy {
    /// Check if the policy is (structurally) valid
    pub fn is_valid(&self) -> bool {
        if self.principals.is_empty() || self.statements.is_empty() {
            return false;
        }

        return !self
            .statements
            .iter()
            .any(|x| x.actions.is_empty() || x.resources.is_empty());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_test::{assert_tokens, Token};

    macro_rules! vec_of_strings {
        ($($x:expr),*) => (vec![$($x.to_string()),*]);
    }

    #[test]
    fn policy_serialization_no_sid() {
        // sid should be left off serialized json when not set
        let policy = Policy {
            sid: None,
            principals: Vec::new(),
            statements: Vec::new(),
        };

        assert_tokens(
            &policy,
            &[
                Token::Struct {
                    name: "Policy",
                    len: 2,
                },
                Token::Str("principals"),
                Token::Seq { len: Some(0) },
                Token::SeqEnd,
                Token::Str("statements"),
                Token::Seq { len: Some(0) },
                Token::SeqEnd,
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn policy_serialization() {
        let policy = Policy {
            sid: Some("my policy".into()),
            principals: vec_of_strings!["user:test"],
            statements: vec![Statement {
                effect: Effect::Allow,
                actions: vec_of_strings!["blog:list"],
                resources: vec_of_strings!["resources:blog:123", "resources:blog:*"],
            }],
        };

        assert_tokens(
            &policy,
            &[
                Token::Struct {
                    name: "Policy",
                    len: 3,
                },
                Token::Str("sid"), // ensure sid is omitted when not specified
                Token::Some,
                Token::Str("my policy"),
                Token::Str("principals"),
                Token::Seq { len: Some(1) },
                Token::Str("user:test"),
                Token::SeqEnd,
                Token::Str("statements"),
                Token::Seq { len: Some(1) },
                Token::Struct {
                    name: "Statement",
                    len: 3,
                },
                Token::Str("effect"),
                Token::UnitVariant {
                    name: "Effect",
                    variant: "allow",
                },
                Token::Str("actions"),
                Token::Seq { len: Some(1) },
                Token::Str("blog:list"),
                Token::SeqEnd,
                Token::Str("resources"),
                Token::Seq { len: Some(2) },
                Token::Str("resources:blog:123"),
                Token::Str("resources:blog:*"),
                Token::SeqEnd,
                Token::StructEnd,
                Token::SeqEnd,
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn policy_is_valid() {
        let mut policy = Policy {
            sid: None,
            principals: Vec::new(),
            statements: Vec::new(),
        };

        assert_eq!(false, policy.is_valid());

        policy.principals.push("user:test".into());
        assert_eq!(false, policy.is_valid());

        let st1 = Statement {
            effect: Effect::Allow,
            actions: vec_of_strings!["blog:list"],
            resources: vec_of_strings!["resources:blog:123", "resources:blog:*"],
        };

        // invalid statement
        let st2 = Statement {
            effect: Effect::Deny,
            actions: vec_of_strings!["account:list"],
            resources: Vec::new(),
        };

        policy.statements.push(st1);
        policy.statements.push(st2);
        assert_eq!(false, policy.is_valid());

        policy.statements[1]
            .resources
            .push("resource:account".into());
        assert_eq!(true, policy.is_valid());
    }
}

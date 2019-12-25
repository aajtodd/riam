use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// Effect indicates whether a policy statement allows or denies access
#[derive(Serialize, Deserialize, Eq, PartialEq, Debug, Clone)]
pub enum Effect {
    /// Allow access
    #[serde(rename = "allow")]
    Allow,

    /// Deny access
    #[serde(rename = "deny")]
    Deny,
}

/// Statement contains information about a single permission
#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct Statement {
    /// An optional statement id. This is used to differentiate statements e.g. "Grant read access to resource:xyz"
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sid: Option<String>,

    /// Allow or Deny the actions
    pub effect: Effect,

    /// One or more actions that apply to the resources
    pub actions: Vec<String>,

    /// The resources the statement applies to
    pub resources: Vec<String>,
}

/// Policy represents an access control policy which is used to either grant or deny a
/// principal (users/groups/roles/etc) actions on specific resources.
#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct Policy {
    /// The unique ID assigned to the policy
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<Uuid>,

    /// The policy name (e.g. "FullAdminAccess")
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,

    /// The body of the policy
    pub statements: Vec<Statement>,
}

impl Policy {
    /// Check if the policy is (structurally) valid
    pub fn is_valid(&self) -> bool {
        // TODO - validate resource names and action names follow whatever grammar we define for them
        return !(self.statements.is_empty()
            || self
                .statements
                .iter()
                .any(|x| x.actions.is_empty() || x.resources.is_empty()));
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
    fn test_statement_serialization_no_sid() {
        // sid should be left off serialized json when not set
        let statement = Statement {
            sid: None,
            effect: Effect::Deny,
            actions: Vec::new(),
            resources: Vec::new(),
        };

        assert_tokens(
            &statement,
            &[
                Token::Struct {
                    name: "Statement",
                    len: 3,
                },
                Token::Str("effect"),
                Token::UnitVariant {
                    name: "Effect",
                    variant: "deny",
                },
                Token::Str("actions"),
                Token::Seq { len: Some(0) },
                Token::SeqEnd,
                Token::Str("resources"),
                Token::Seq { len: Some(0) },
                Token::SeqEnd,
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn test_policy_serialization() {
        let policy = Policy {
            name: Some("my policy".into()),
            id: None,
            statements: vec![Statement {
                sid: Some("my statement".into()),
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
                    len: 2,
                },
                Token::Str("name"),
                Token::Some,
                Token::Str("my policy"),
                Token::Str("statements"),
                Token::Seq { len: Some(1) },
                Token::Struct {
                    name: "Statement",
                    len: 4,
                },
                Token::Str("sid"),
                Token::Some,
                Token::Str("my statement"),
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
    fn test_policy_is_valid() {
        let mut policy = Policy {
            name: None,
            id: None,
            statements: Vec::new(),
        };

        assert_eq!(false, policy.is_valid());

        let st1 = Statement {
            sid: None,
            effect: Effect::Allow,
            actions: vec_of_strings!["blog:list"],
            resources: vec_of_strings!["resources:blog:123", "resources:blog:*"],
        };

        // invalid statement
        let st2 = Statement {
            sid: None,
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

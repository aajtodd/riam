use crate::conditions::Eval;
use crate::wildcard;
use crate::{AuthRequest, Effect, Policy, Result};
use uuid::Uuid;

/// Manage creation, storage/retrieval, and deletion of policies.
pub trait PolicyManager {
    /// Create and store a new policy. The policy ID is returned
    fn create(&mut self, policy: Policy) -> Result<Uuid>;

    /// Update an existing policy
    fn update(&mut self, policy: &Policy) -> Result<()>;

    /// Delete a policy
    ///
    /// Note: This will detach the policy from all principals it is currently used by
    fn delete(&mut self, id: &Uuid) -> Result<()>;

    /// Get a policy by id
    fn get(&self, id: &Uuid) -> Result<&Policy>;

    /// List all policies
    fn list(&self) -> Result<Vec<Policy>>;

    /// Attach a policy to a principal
    fn attach(&mut self, principal: &str, id: &Uuid) -> Result<()>;

    /// Detach a policy from a principal
    fn detach(&mut self, principal: &str, id: &Uuid) -> Result<()>;

    /// Get all policies for a given principal
    fn get_policies_for_principal(&self, principal: &str) -> Result<Option<Vec<Policy>>>;
}

/// Engine implements the logic to check if a specific request (action)
/// by a principal is allowed or not on a particular resource.
///
/// An action is allowed if and only if there is an explicit "allow" statement that can be applied. Any explicit "deny" statements will override an "allow".
/// If no statement matches then a request is implicitly denied by default.
///
pub struct Engine<T: PolicyManager> {
    /// The underlying policy manager/storage mechanism
    pub manager: T,
}

impl<T: PolicyManager> Engine<T> {
    /// Create a new engine with the given policy manager
    pub fn new(manager: T) -> Self {
        Engine { manager }
    }

    /// Check if an action is allowed or not
    pub fn is_allowed(&self, req: &AuthRequest) -> Result<bool> {
        let policies = self.manager.get_policies_for_principal(&req.principal)?;

        if policies.is_none() {
            // no policies for the given principal
            return Ok(false);
        }
        let policies = policies.unwrap();

        let mut allowed = false;

        // we have to iterate over all the policies since policy statements may be contradictory
        // (e.g. one allows, another explicitly denies). Explicit denies take precedence.
        for p in policies.iter() {
            // check the policy statements
            for stmt in p.statements.iter() {
                // check if any of the actions match
                if !stmt.actions.iter().any(|action| wildcard::matches(action, &req.action)) {
                    continue;
                }

                // check if any of the resources match
                if !stmt
                    .resources
                    .iter()
                    .any(|resource| wildcard::matches(resource, &req.resource))
                {
                    continue;
                }

                // check the conditions
                match stmt.conditions {
                    Some(ref conditions) => {
                        // conditions are AND'd together and must all match
                        if !conditions.iter().all(|c| c.evaluate(&req.context)) {
                            continue;
                        }
                    }
                    None => {}
                }

                // the current statement is a candidate, check the intended effect
                match stmt.effect {
                    Effect::Allow => {
                        allowed = true;
                    }
                    Effect::Deny => {
                        // explicit deny
                        return Ok(false);
                    }
                }
            }
        }

        Ok(allowed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::managers::MemoryManager;

    #[cfg(feature = "nightly")]
    use test::Bencher;

    #[test]
    fn test_engine_is_allowed() {
        // simple smoke test, no conditions
        let mut engine = Engine::new(MemoryManager::new());

        let jsp = r#"
        {
            "name": "Account policy",
            "statements": [
                {
                    "sid": "Grant account list access",
                    "effect": "allow",
                    "actions": ["account:list"],
                    "resources": ["resource:account:*"]
                },
                {
                    "sid": "Deny root account access",
                    "effect": "deny",
                    "actions": ["account:list"],
                    "resources": ["resource:account:123"]
                },
                {
                    "sid": "Grant all read access on specific account",
                    "effect": "allow",
                    "actions": "account:describe:*",
                    "resources": "resource:account:789"
                }
            ]
        }
        "#;

        let policy: Policy = serde_json::from_str(jsp).unwrap();
        let id = engine.manager.create(policy).unwrap();
        let principal = "user:test-user";
        engine.manager.attach(principal, &id).unwrap();

        #[rustfmt::skip]
        let cases = vec![
            // principal, action, resource, expected
            ( "user:test-user", "account:list", "resource:account:567", true,), // statement 1
            ( "user:test-user", "account:list", "resource:account:789", true,), // statement 1
            ( "user:test-user-2", "account:list", "resource:account:789", false,), // non-existent principal
            ( "user:test-user", "account:list", "resource:account:123", false,), // statement 2 (explicit deny w/allowed match on other statements)
            ( "user:test-user", "account:describe:limits", "resource:account:123", false,), // no matching statements
            ( "user:test-user", "account:describe:limits", "resource:account:789", true,), // statement 3
        ];
        for x in cases {
            let (principal, action, resource, expected) = x;
            let req = AuthRequest::new(principal, action, resource);

            let actual = engine.is_allowed(&req).unwrap();
            assert_eq!(expected, actual, "req: {:?}", req);
        }
    }

    #[cfg(feature = "nightly")]
    #[bench]
    fn bench_is_allowed(b: &mut Bencher) {
        let mut engine = Engine::new(MemoryManager::new());
        let jsp = r#"
        {
            "name": "Account policy",
            "statements": [
                {
                    "sid": "Grant account list access",
                    "effect": "allow",
                    "actions": ["account:list"],
                    "resources": ["resource:account:*"]
                },
                {
                    "sid": "Deny root account access",
                    "effect": "deny",
                    "actions": ["account:list"],
                    "resources": ["resource:account:123"]
                },
                {
                    "sid": "Grant all read access on specific account",
                    "effect": "allow",
                    "actions": ["account:describe:*"],
                    "resources": ["resource:account:789"]
                }
            ]
        }
        "#;

        let policy: Policy = serde_json::from_str(jsp).unwrap();
        let id = engine.manager.create(policy).unwrap();
        let principal = "user:test-user";
        engine.manager.attach(principal, &id).unwrap();

        let (principal, action, resource) = ("user:test-user", "account:describe:limits", "resource:account:789");

        // Statement 3
        let req = AuthRequest::new(principal, action, resource);

        b.iter(|| engine.is_allowed(&req));
    }
}

use crate::{Policy, PolicyManager, Result, RiamError};
use std::collections::HashMap;
use std::collections::HashSet;
use uuid::Uuid;

/// An in-memory implemntation of a policy manager
pub struct MemoryManager {
    // principal -> policy_id's
    by_principal: HashMap<String, HashSet<Uuid>>,

    // policy-id -> Policy
    by_id: HashMap<Uuid, Policy>,
}

impl MemoryManager {
    /// Create a new in-memory manager
    pub fn new() -> Self {
        MemoryManager {
            by_principal: HashMap::new(),
            by_id: HashMap::new(),
        }
    }
}

impl PolicyManager for MemoryManager {
    /// Create and store a new policy
    fn create(&mut self, mut policy: Policy) -> Result<Uuid> {
        if !policy.is_valid() {
            return Err(RiamError::InvalidPolicy);
        }

        // create a new policy ID
        let id = Uuid::new_v4();
        policy.id = Some(id);
        self.by_id.insert(id, policy);
        Ok(id)
    }

    /// Update an existing policy
    fn update(&mut self, policy: &Policy) -> Result<()> {
        match policy.id {
            Some(id) => match self.by_id.get_mut(&id) {
                Some(p) => {
                    *p = policy.clone();
                }
                None => return Err(RiamError::UnknownPolicy),
            },
            None => return Err(RiamError::InvalidPolicy),
        }
        Ok(())
    }

    /// Get a policy by id
    fn get(&self, id: &Uuid) -> Result<&Policy> {
        if let Some(p) = self.by_id.get(&id) {
            return Ok(p);
        }

        Err(RiamError::UnknownPolicy)
    }

    /// Delete a policy
    fn delete(&mut self, id: &Uuid) -> Result<()> {
        if let Some(_) = self.by_id.remove(&id) {
            self.by_principal.retain(|_principal, pset| {
                pset.remove(&id);
                return pset.len() > 0;
            })
        } else {
            return Err(RiamError::UnknownPolicy);
        }
        Ok(())
    }

    /// List all policies
    fn list(&self) -> Result<Vec<Policy>> {
        Ok(Vec::new())
    }

    /// Get all policies for a given principal
    fn get_policies_for_principal(&self, principal: &str) -> Result<Option<Vec<Policy>>> {
        if let Some(policy_ids) = self.by_principal.get(principal) {
            let mut policies: Vec<Policy> = Vec::with_capacity(policy_ids.len());
            for id in policy_ids {
                let p = self.by_id.get(id).unwrap();
                policies.push(p.clone());
            }
            return Ok(Some(policies));
        }
        Ok(None)
    }

    /// Attach a policy to a principal
    fn attach(&mut self, principal: &str, id: &Uuid) -> Result<()> {
        self.by_principal
            .entry(principal.to_owned())
            .or_insert(HashSet::new())
            .insert(*id);
        Ok(())
    }

    /// Detach a policy from a principal
    fn detach(&mut self, principal: &str, id: &Uuid) -> Result<()> {
        if let Some(pset) = self.by_principal.get_mut(principal) {
            pset.remove(id);
            if pset.len() == 0 {
                self.by_principal.remove(principal);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_memory_manager_attach_detach() {
        let mut mgr = MemoryManager::new();

        let jsp = r#"
        {
            "name": "Account policy",
            "statements": [
                {
                    "sid": "Grant account access",
                    "effect": "allow",
                    "actions": ["account:list", "account:get"],
                    "resources": ["resource:account:1235"]
                }
            ]
        }
        "#;

        let policy: Policy = serde_json::from_str(jsp).unwrap();
        let id = mgr.create(policy).unwrap();
        let principal = "user:test-user";
        mgr.attach(principal, &id).unwrap();
        let actual = mgr.get_policies_for_principal(principal).unwrap().unwrap();

        assert_eq!(actual.len(), 1);

        mgr.detach(principal, &id).unwrap();

        let actual = mgr.get_policies_for_principal(principal).unwrap();

        assert_eq!(actual.is_none(), true);
    }

    #[test]
    fn test_memory_manager_update() {
        let mut mgr = MemoryManager::new();

        let jsp = r#"
        {
            "name": "Account policy",
            "statements": [
                {
                    "sid": "Grant account access",
                    "effect": "allow",
                    "actions": ["account:list", "account:get"],
                    "resources": ["resource:account:1235"]
                }
            ]
        }
        "#;

        let policy: Policy = serde_json::from_str(jsp).unwrap();
        let id = mgr.create(policy).unwrap();

        let mut policy = mgr.get(&id).unwrap().clone();
        assert_eq!(policy.name, Some("Account policy".to_owned()));

        policy.name = Some("Modified Name".to_owned());
        mgr.update(&policy).unwrap();

        let policy = mgr.get(&id).unwrap().clone();
        assert_eq!(policy.name, Some("Modified Name".to_owned()));
    }

    #[test]
    fn test_memory_manager_delete() {
        let mut mgr = MemoryManager::new();

        let jsp = r#"
        {
            "name": "Account policy",
            "statements": [
                {
                    "sid": "Grant account access",
                    "effect": "allow",
                    "actions": ["account:list", "account:get"],
                    "resources": ["resource:account:1235"]
                }
            ]
        }
        "#;

        let p1: Policy = serde_json::from_str(jsp).unwrap();
        let id1 = mgr.create(p1).unwrap();
        let jsp = r#"
        {
            "name": "Blog policy",
            "statements": [
                {
                    "sid": "Deny blog access",
                    "effect": "deny",
                    "actions": ["blog:list"],
                    "resources": ["resource:blog:*"]
                }
            ]
        }
        "#;

        let p2: Policy = serde_json::from_str(jsp).unwrap();
        let id2 = mgr.create(p2).unwrap();

        let principal = "users:test-user";
        mgr.attach(principal, &id1).unwrap();
        mgr.attach(principal, &id2).unwrap();

        let actual = mgr.get_policies_for_principal(principal).unwrap().unwrap();
        assert_eq!(actual.len(), 2);

        mgr.delete(&id1).unwrap();

        let actual = mgr.get_policies_for_principal(principal).unwrap().unwrap();
        assert_eq!(actual.len(), 1);
    }
}

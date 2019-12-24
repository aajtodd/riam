use crate::Policy;
use crate::Result;
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
    fn get(&mut self, id: &Uuid) -> Result<&Policy>;

    /// List all policies
    fn list(&mut self) -> Result<Vec<Policy>>;

    /// Attach a policy to a principal
    fn attach(&mut self, principal: &str, id: &Uuid) -> Result<()>;

    /// Detach a policy from a principal
    fn detach(&mut self, principal: &str, id: &Uuid) -> Result<()>;

    /// Get all policies for a given principal
    fn get_policies_for_principal(&mut self, principal: &str) -> Result<Option<Vec<Policy>>>;
}

/// Engine implements the logic to check if a specific request (action)
/// by a principal is allowed or not on a particular resource.
///
/// An action is allowed if and only if there is an explicit "allow" statement that can be applied. Any explicit "deny" statements will override an "allow".
/// If no statement matches then a request is implicitly denied by default.
///
pub struct Engine<T: PolicyManager> {
    manager: T,
}

impl<T: PolicyManager> Engine<T> {
    /// Create a new engine with the given policy manager
    pub fn new(manager: T) -> Self {
        Engine { manager: manager }
    }

    /// Check if an action is allowed or not
    pub fn is_allowed(&mut self /* request */) -> Result<bool> {
        unimplemented!();
    }
}

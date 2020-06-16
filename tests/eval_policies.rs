#![warn(rust_2018_idioms)]

use riam::managers::MemoryManager;
use riam::{AuthRequest, Engine, Policy, PolicyManager};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct PolicyTest {
    name: String,
    allowed: bool,
    request: AuthRequest,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct TestFixture {
    principals: HashMap<String, Vec<String>>,
    tests: Vec<PolicyTest>,
    policies: Vec<Policy>,
}

#[test]
fn engine_is_allowed() {
    // policies.json contains a set of policies, principals and the policies that they are attached
    // to, and a list of authorization requests with their expected result for the set of
    // principals/policies defined in the file
    let jsp = include_str!("./policies.json");
    let fixture: TestFixture = serde_json::from_str(jsp).expect("policies.json is invalid");

    let mut policy_by_name: HashMap<String, Uuid> = HashMap::new();
    let mut mgr = MemoryManager::new();
    for p in fixture.policies.into_iter() {
        let name = p.name.clone().unwrap();
        let id = mgr.create(p).unwrap();
        policy_by_name.insert(name, id);
    }

    for (principal, policies) in fixture.principals {
        policies.iter().for_each(|name| {
            let id = policy_by_name
                .get(name)
                .expect(&format!("no policy named: {} exists", name));
            mgr.attach(&principal, &id).unwrap();
        })
    }

    let engine = Engine::new(mgr);
    for (i, test) in fixture.tests.iter().enumerate() {
        let actual = engine.is_allowed(&test.request).expect(&format!(
            "unexpected error evaluating policy for test[{}] '{}'",
            i, test.name
        ));
        assert_eq!(test.allowed, actual, "policy test[{}] '{}' failed", i, test.name);
    }
}

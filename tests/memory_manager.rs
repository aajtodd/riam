#![warn(rust_2018_idioms)]

use riam::managers::MemoryManager;
use riam::{Policy, PolicyManager};

#[test]
fn get_policies_by_principal() {
    let jsp = r#"
    [
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
        },
        {
            "name": "Blog policy",
            "statements": [
                {
                    "effect": "allow",
                    "actions": ["blog:list", "blog:get"],
                    "resources": ["resource:blog:*"]
                }
            ]
        },
        {
            "name": "S3 policy",
            "statements": [
                {
                    "sid": "Grant S3 read",
                    "effect": "allow",
                    "actions": ["s3:list"],
                    "resources": ["resource:s3:bucket:*"]
                }
            ]
        }
    ]
    "#;

    let policies: Vec<Policy> = serde_json::from_str(jsp).unwrap();

    let mut mgr = MemoryManager::new();
    for p in policies.into_iter() {
        let principal = if p.name.as_ref().unwrap().contains("Blog") {
            "users:test-user-1"
        } else {
            "users:test-user-2"
        };

        let id = mgr.create(p).unwrap();
        mgr.attach(&principal, &id);
    }

    let actual = mgr
        .get_policies_for_principal("users:test-user-2")
        .unwrap()
        .unwrap();

    assert_eq!(actual.len(), 2);
}

#![warn(rust_2018_idioms)]

use riam::conditions::{self, Eval};
use riam::Context;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct PolicyTest {
    name: String,
    expected: bool,
    context: Context,
    conditions: Vec<conditions::Condition>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct TestFixture {
    tests: Vec<PolicyTest>,
}

#[test]
fn eval_conditions() {
    // conditions.json contains a test suite of conditions and contexts
    let jsp = include_str!("./conditions.json");
    let fixture: TestFixture = serde_json::from_str(jsp).expect("conditions.json is invalid");

    for (i, test) in fixture.tests.iter().enumerate() {
        let actual = test.conditions.iter().all(|c| c.evaluate(&test.context));
        assert_eq!(
            test.expected, actual,
            "condition test[{}] '{}' failed",
            i, test.name
        );
    }
}

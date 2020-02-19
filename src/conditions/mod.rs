//! Policy Conditions
//!
//! The Condition element (or Condition block) lets you specify conditions for when a policy is in effect. The Condition element is optional.
//! In the Condition element, you build expressions in which you use condition operators (equal, less than, etc.) to match the condition keys and values
//! in the policy against keys and values in the authorization request context. To learn more about the request context, see [Context](crate::Context).
//!
//!
//! # Evaluation of condition's with multiple keys and/or multiple values
//!
//! If your policy has multiple condition operators or multiple keys attached to a single condition operator, the conditions are evaluated using a logical AND.
//! If a single condition operator includes multiple values for one key, that condition operator is evaluated using a logical OR. All conditions must resolve
//! to true to trigger the desired Allow or Deny effect.
//!
//! ## Example:
//!
//! ```text
//!    "StringEquals": {
//!        "key1": "value1",
//!        "key2": ["value2, value3"]
//!    },
//!    "DateBefore": {
//!        "riam:currentTime": "2019/07/22:00:00:00Z"
//!    }
//! ```
//!
//! - The `StringEquals` and the `DateBefore` conditions are AND'd together.
//! - The `StringEquals` `key1` and `key2` conditions are AND'd together (both key1 and key2 must be present and match their values)
//! - The `StringEquals` `key2` condition can be either `value1` or `value2`
//!
//!
//! # String Operators
//!
//! String condition operators let you construct Condition elements that restrict access based on comparing a key to a string value.
//!
//!
//! For example, the following statement contains a Condition element that uses the [`StringEquals`] condition operator with a key `UserAgent` to
//! specify that the request must include a specific value in the user agent header.
//!
//! ```text
//! {
//!   "statements": {
//!     "effect": "allow",
//!     "actions": "iam:*AccessKey*",
//!     "resources": "arn:aws:iam::user/*",
//!     "conditions": [
//!         {"StringEquals": {"UserAgent": "Example Corp Java Client"}}
//!     ]
//!   }
//! }
//!
//! ```
//!
//! The following request would be allowed (assuming the policy is attached to the principal):
//!
//! ```text
//! {
//!     "principal": "users:johndoe",
//!     "action": "iam:GetAccessKey",
//!     "resource": "arn:aws:iam::user/key1",
//!     "context": {
//!         "UserAgent": "Example Corp Java Client"
//!     }
//! }
//!
//! ```

mod boolean;
mod condition;
mod string;

pub use condition::{Condition, Eval};
pub use string::{
    StringEquals, StringEqualsIgnoreCase, StringLike, StringNotEquals, StringNotEqualsIgnoreCase, StringNotLike,
};

pub use boolean::Bool;

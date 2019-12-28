#![cfg_attr(all(test, feature = "nightly"), feature(test))]
#![deny(missing_docs)]
//! # riam
//! riam is a decision/policy engine inspired by AWS IAM policies.
//!
//! See the [REPO] README for additional information.
//!
//! [REPO]: https://github.com/aajtodd/riam

#[cfg(all(test, feature = "nightly"))]
extern crate test;

pub mod condition;
mod engine;
mod error;
pub mod managers;
mod policy;
mod request;
mod wildcard;

pub use engine::{Engine, PolicyManager};
pub use error::{Result, RiamError};
pub use policy::{Effect, Policy, Statement};
pub use request::AuthRequest;

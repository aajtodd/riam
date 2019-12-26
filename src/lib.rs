#![cfg_attr(all(test, feature = "nightly"), feature(test))]
#![deny(missing_docs)]
//! A decision/policy engine inspired by AWS IAM policies

#[cfg(all(test, feature = "nightly"))]
extern crate test;

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

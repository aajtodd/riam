#![deny(missing_docs)]
//! A decision/policy engine inspired by AWS IAM policies

#![feature(test)]
extern crate test;

mod engine;
mod error;
pub mod managers;
mod policy;
mod wildcard;

pub use engine::{Engine, PolicyManager};
pub use error::{Result, RiamError};
pub use policy::Policy;

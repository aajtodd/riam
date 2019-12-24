#![deny(missing_docs)]
//! A decision/policy engine inspired by AWS IAM policies

mod engine;
mod error;
pub mod managers;
mod policy;

pub use engine::{Engine, PolicyManager};
pub use error::{Result, RiamError};
pub use policy::Policy;

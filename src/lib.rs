#![deny(missing_docs)]
//! A decision/policy engine inspired by AWS IAM policies

mod error;
mod policy;

pub use error::{Result, RiamError};
pub use policy::Policy;

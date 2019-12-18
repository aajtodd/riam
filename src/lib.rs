#![deny(missing_docs)]
//! A decision/policy engine inspired by AWS IAM policies

mod error;

pub use error::{Result, RiamError};

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}

use failure::Fail;
use std::io;

/// Error type for riam
#[derive(Fail, Debug)]
pub enum RiamError {
    /// IO error
    #[fail(display = "IO error: {}", _0)]
    Io(#[cause] io::Error),

    /// Serialization or deserialization error
    #[fail(display = "serde_json error: {}", _0)]
    Serde(#[cause] serde_json::Error),
}

impl From<io::Error> for RiamError {
    fn from(err: io::Error) -> RiamError {
        RiamError::Io(err)
    }
}

impl From<serde_json::Error> for RiamError {
    fn from(err: serde_json::Error) -> RiamError {
        RiamError::Serde(err)
    }
}

/// Result type for riam
pub type Result<T> = std::result::Result<T, RiamError>;

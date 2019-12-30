use std::collections::HashMap;

// TODO - ideally we wouldn't be constrained to just key/value context but deserializing arbitrary
// JSON into Map<String, serde_json::Value> is going to be more difficult to deal with. For now
// let's get this library working even if it comes with some caveats.
// TODO - move to request module
/// Authorization request context. Consists of key/value pairs that the caller is expected to
/// gather and send with a request to enable condition evaluation. A policy that has conditions
/// will fail if the context is missing.
pub struct Context(pub HashMap<String, String>);

/// AuthRequest represents an attempted action on a resource. It describes who, what, and how
/// the resource in question is to be accessed and is used to make authorization decisions.
#[derive(Debug)]
pub struct AuthRequest {
    /// The subject (user/group/etc) attempting the action
    pub principal: String,

    /// The name of the action being taken
    pub action: String,

    /// The resources being acted upon
    pub resource: String,
}

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

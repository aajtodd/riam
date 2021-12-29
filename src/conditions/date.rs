use super::{Eval};
use crate::conditions::condition::{Body, EvalModifier};
use crate::Context;
use chrono::{DateTime, Utc};

use serde::{Deserialize, Serialize};


type UtcDateTime = DateTime<Utc>;

/// Exact date
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct DateEquals {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<UtcDateTime>,
}

impl_cond_base!(DateEquals, UtcDateTime);

impl Eval for DateEquals {
    fn evaluate(&self, _ctx: &Context) -> bool {
        unimplemented!()
    }
}

/// Negated matching
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct DateNotEquals {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<UtcDateTime>,
}

impl_cond_base!(DateNotEquals, UtcDateTime);

impl Eval for DateNotEquals {
    fn evaluate(&self, _ctx: &Context) -> bool {
        unimplemented!()
    }
}

/// Match before a specific date and time
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct DateBefore {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<UtcDateTime>,
}

impl_cond_base!(DateBefore, UtcDateTime);

impl Eval for DateBefore {
    fn evaluate(&self, _ctx: &Context) -> bool {
        unimplemented!()
    }
}

/// Matching at or before a specific date and time
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct DateAtOrBefore {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<UtcDateTime>,
}

impl_cond_base!(DateAtOrBefore, UtcDateTime);

impl Eval for DateAtOrBefore {
    fn evaluate(&self, _ctx: &Context) -> bool {
        unimplemented!()
    }
}

/// Match after a specific date and time
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct DateAfter {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<UtcDateTime>,
}

impl_cond_base!(DateAfter, UtcDateTime);

impl Eval for DateAfter {
    fn evaluate(&self, _ctx: &Context) -> bool {
        unimplemented!()
    }
}

/// Matching at or after a specific date and time
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct DateAtOrAfter {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<UtcDateTime>,
}

impl_cond_base!(DateAtOrAfter, UtcDateTime);

impl Eval for DateAtOrAfter {
    fn evaluate(&self, _ctx: &Context) -> bool {
        unimplemented!()
    }
}

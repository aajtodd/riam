use crate::conditions::condition::{EvalModifier, Body};
use crate::Context;
use crate::conditions::Eval;
use ipnet::IpNet;

use serde::{Deserialize, Serialize};

/// Match the specified IP address or range
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct IpAddress {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    // FIXME - maybe we should just take a string here?
    #[serde(flatten)]
    body: Body<IpNet>,
}

impl_cond_base!(IpAddress, IpNet);

impl Eval for IpAddress {
    fn evaluate(&self, _ctx: &Context) -> bool {
        unimplemented!()
    }
}

/// All IP addresses except the specified IP address or range
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct NotIpAddress {
    #[serde(skip)]
    modifier: Option<EvalModifier>,

    #[serde(flatten)]
    body: Body<IpNet>,
}

impl_cond_base!(NotIpAddress, IpNet);

impl Eval for NotIpAddress {
    fn evaluate(&self, _ctx: &Context) -> bool {
        unimplemented!()
    }
}

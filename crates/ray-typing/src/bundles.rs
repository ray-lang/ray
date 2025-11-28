use std::collections::HashMap;

use ray_shared::node_id::NodeId;

use crate::{binding_groups::BindingId, constraints::Constraint, types::Ty};

#[derive(Clone, Debug)]
pub struct BindingBundle {
    pub binding: BindingId,
    pub constraints: Vec<Constraint>,
    pub givens: Vec<Constraint>, // lexical givens at def site (can be empty for now)
    pub ret_ty: Option<Ty>,      // can be None for now
    pub root_expr: NodeId,       // for debugging/anchoring
}

#[derive(Clone, Debug)]
pub struct BundleStore {
    pub by_binding: HashMap<BindingId, BindingBundle>,
}

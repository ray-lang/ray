use serde::{Deserialize, Serialize};

use crate::{
    local_binding::LocalBindingId,
    resolution::DefTarget,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SymbolRole {
    Definition,
    Reference,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SymbolIdentity {
    Def(DefTarget),
    Local(LocalBindingId),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SymbolTarget {
    pub identity: SymbolIdentity,
    pub role: SymbolRole,
}

impl SymbolTarget {
    pub fn new(identity: SymbolIdentity, role: SymbolRole) -> Self {
        Self { identity, role }
    }
}

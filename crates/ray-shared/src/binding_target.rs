use serde::{Deserialize, Serialize};

use crate::{def::DefId, local_binding::LocalBindingId};

/// Target of a binding - either a local binding or a top-level definition.
/// This unifies the two kinds of bindings for storage in shared maps.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BindingTarget {
    /// A local binding (parameter, let-binding, etc.)
    Local(LocalBindingId),
    /// A top-level definition (function, struct, etc.)
    Def(DefId),
}

impl From<LocalBindingId> for BindingTarget {
    fn from(id: LocalBindingId) -> Self {
        BindingTarget::Local(id)
    }
}

impl From<DefId> for BindingTarget {
    fn from(id: DefId) -> Self {
        BindingTarget::Def(id)
    }
}

impl std::fmt::Display for BindingTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BindingTarget::Local(id) => write!(f, "Local({})", id),
            BindingTarget::Def(id) => write!(f, "Def({})", id),
        }
    }
}

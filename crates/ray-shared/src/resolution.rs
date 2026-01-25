use serde::{Deserialize, Serialize};

use crate::{
    def::{DefId, LibraryDefId},
    local_binding::LocalBindingId,
    type_param_id::TypeParamId,
};

/// The result of resolving a name reference in the AST.
///
/// Each name usage in the source code resolves to one of these variants,
/// stored in a side-table indexed by NodeId.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Resolution {
    /// Reference to a top-level definition (function, struct, trait, etc.)
    Def(DefTarget),
    /// Reference to a local binding (parameter, let-binding)
    Local(LocalBindingId),
    /// A type parameter in scope
    TypeParam(TypeParamId),
    /// Name could not be resolved (error case)
    Error,
}

/// Target of a definition reference.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DefTarget {
    /// Definition in this workspace, identified by DefId.
    Workspace(DefId),
    /// Definition from a compiled library (.raylib).
    Library(LibraryDefId),
}

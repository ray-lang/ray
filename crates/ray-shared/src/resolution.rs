use serde::{Deserialize, Serialize};

use crate::{
    def::{DefId, LibraryDefId},
    local_binding::LocalBindingId,
    pathlib::{ItemPath, ModulePath},
    type_param_id::TypeParamId,
};

/// The category of name being resolved.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NameKind {
    /// A type name (in type annotations, struct fields, etc.)
    Type,
    /// A value name (function call, variable reference, struct literal, etc.)
    Value,
}

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
    Error { name: String, kind: NameKind },
}

impl Resolution {
    /// Extract the `DefTarget` if this resolution points to a definition.
    pub fn to_def_target(&self) -> Option<DefTarget> {
        match self {
            Resolution::Def(target) => Some(target.clone()),
            _ => None,
        }
    }
}

/// Target of a definition reference.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DefTarget {
    /// Definition in this workspace, identified by DefId.
    Workspace(DefId),
    /// Definition from a compiled library (.raylib).
    Library(LibraryDefId),
    /// A primitive/builtin type (int, bool, char, uint, etc.).
    Primitive(ItemPath),
    /// A module re-exported as a namespace.
    Module(ModulePath),
}

impl DefTarget {
    /// Extract the `DefId` if this is a workspace definition.
    pub fn as_workspace(&self) -> Option<DefId> {
        match self {
            DefTarget::Workspace(def_id) => Some(*def_id),
            _ => None,
        }
    }
}

use serde::{Deserialize, Serialize};

use crate::{file_id::FileId, node_id::NodeId, pathlib::ModulePath, span::Span};

/// Identifies a top-level definition in the program.
///
/// DefIds are structural: they identify a definition by its location (file +
/// index within file), not by its name. This makes them stable across renames
/// and decouples identity from name resolution.
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct DefId {
    /// The file containing this definition.
    pub file: FileId,
    /// Index of this definition within the file (in source order).
    pub index: u32,
}

impl std::fmt::Display for DefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DefId(file={}, local_index={})", self.file, self.index)
    }
}

impl DefId {
    pub fn new(file: FileId, index: u32) -> DefId {
        DefId { file, index }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct LibraryDefId {
    /// The module containing this definition.
    pub module: ModulePath,
    /// Index of this definition with the library module.
    pub index: u32,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DefHeader {
    pub def_id: DefId,
    pub root_node: NodeId,
    pub name: String,
    pub kind: DefKind,
    pub span: Span,
    pub name_span: Span,       // Span of just the name (for rename)
    pub parent: Option<DefId>, // For methods: the impl/trait DefId
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum DefKind {
    FileMain, // Top-level execution context (index: 0)
    Function { signature: SignatureStatus },
    Binding { annotated: bool, mutable: bool },
    AssociatedConst { annotated: bool }, // annotated: true if type is explicit
    Method,                              // Always has explicit signature (from trait or explicit)
    Primitive,
    Struct,
    StructField, // A field within a struct (parent is the struct DefId)
    Trait,
    Impl,
    TypeAlias,
    Test,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SignatureStatus {
    FullyAnnotated, // All parameter and return types explicit
    ReturnElided,   // Parameters annotated, return type inferred from => body
    ImplicitUnit,   // Parameters annotated, block body, no return type (implicit ())
    Unannotated,    // Missing parameter or return type annotations
}

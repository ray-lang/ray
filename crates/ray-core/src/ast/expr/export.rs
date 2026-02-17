use std::fmt::Display;

use itertools::Itertools;
use ray_shared::{pathlib::Path, span::Span};
use serde::{Deserialize, Serialize};

use crate::ast::Node;

/// The kind of export statement.
///
/// Mirrors `ImportKind` without `CImport`. Represents re-exports of names
/// from other modules.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExportKind {
    /// `export utils` - re-export the module as a namespace
    Path(Node<Path>),
    /// `export utils with decode, to_url` - selectively re-export specific names
    Names(Node<Path>, Vec<Node<Path>>),
    /// `export utils with *` - re-export all exports from the module
    Glob(Node<Path>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Export {
    pub kind: ExportKind,
    pub span: Span,
}

impl Display for Export {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            ExportKind::Path(path) => write!(f, "export {}", path),
            ExportKind::Names(path, names) => {
                write!(f, "export {} with {}", path, names.iter().join(", "))
            }
            ExportKind::Glob(path) => write!(f, "export {} with *", path),
        }
    }
}

impl Export {
    pub fn path(&self) -> &Path {
        match &self.kind {
            ExportKind::Path(path) => path,
            ExportKind::Names(path, _) => path,
            ExportKind::Glob(path) => path,
        }
    }

    pub fn names(&self) -> Option<&Vec<Node<Path>>> {
        match &self.kind {
            ExportKind::Names(_, names) => Some(names),
            ExportKind::Path(_) | ExportKind::Glob(_) => None,
        }
    }
}

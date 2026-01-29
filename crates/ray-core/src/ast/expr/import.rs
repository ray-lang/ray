use std::{fmt::Display, ops::Deref};

use itertools::Itertools;
use ray_shared::pathlib::Path;

use crate::ast::Node;
use ray_shared::span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportKind {
    /// `import core::io` - namespace handle, access via `io::NAME`
    Path(Node<Path>),
    /// `import core::io with read, write` - selective import
    Names(Node<Path>, Vec<Node<Path>>),
    /// `import core::io with *` - glob import, all exports directly accessible
    Glob(Node<Path>),
    /// `import "C" "header.h"` - C header import
    CImport(String, Span), // second value is the span of the string
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Import {
    pub kind: ImportKind,
    pub span: Span,
}

impl Display for Import {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            ImportKind::Path(path) => write!(f, "{}", path),
            ImportKind::Names(path, names) => {
                write!(f, "{} with {}", path, names.iter().join(", "))
            }
            ImportKind::Glob(path) => write!(f, "{} with *", path),
            ImportKind::CImport(name, _) => write!(f, "import \"C\" {}", name),
        }
    }
}

impl Import {
    pub fn path(&self) -> &Path {
        match &self.kind {
            ImportKind::Path(path) => path,
            ImportKind::Names(path, _) => path.deref(),
            ImportKind::Glob(path) => path.deref(),
            ImportKind::CImport(_, _) => panic!("CImport"),
        }
    }

    pub fn names(&self) -> Option<&Vec<Node<Path>>> {
        match &self.kind {
            ImportKind::Names(_, names) => Some(names),
            ImportKind::Path(_) | ImportKind::Glob(_) | ImportKind::CImport(_, _) => None,
        }
    }
}

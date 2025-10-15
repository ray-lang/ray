use std::{fmt::Display, ops::Deref};

use itertools::Itertools;

use crate::{
    ast::{Node, Path},
    span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportKind {
    Path(Node<Path>),
    Names(Node<Path>, Vec<Node<Path>>),
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
            ImportKind::CImport(name, _) => write!(f, "import \"C\" {}", name),
        }
    }
}

impl Import {
    pub fn path(&self) -> &Path {
        match &self.kind {
            ImportKind::Path(path) => path,
            ImportKind::Names(path, _) => path.deref(),
            ImportKind::CImport(_, _) => panic!("CImport"),
        }
    }

    pub fn names(&self) -> Option<&Vec<Node<Path>>> {
        match &self.kind {
            ImportKind::Names(_, names) => Some(names),
            ImportKind::Path(_) | ImportKind::CImport(_, _) => None,
        }
    }
}

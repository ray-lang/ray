use std::{
    fmt::Display,
    ops::{Deref, DerefMut},
};

use crate::pathlib::{FilePath, Path};
use serde::{Deserialize, Serialize};

use super::Span;

#[derive(Clone, Debug, Default, Hash, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Source {
    pub filepath: FilePath,
    pub span: Option<Span>,
    pub path: Path,
    pub src_module: Path,
}

impl std::fmt::Display for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(span) = &self.span {
            write!(f, "{}:{}", self.filepath, span)
        } else {
            write!(f, "{}", self.filepath)
        }
    }
}

impl From<FilePath> for Source {
    fn from(filepath: FilePath) -> Self {
        let src_module = Path::from(filepath.clone());
        Self {
            filepath,
            src_module,
            span: None,
            path: Path::new(),
        }
    }
}

impl Source {
    pub fn new(filepath: FilePath, span: Span, path: Path, src_module: Path) -> Source {
        Source {
            filepath,
            span: Some(span),
            path,
            src_module,
        }
    }

    pub fn extend_to(&self, other: &Source) -> Source {
        let span = match (self.span, other.span) {
            (Some(a), Some(b)) => Some(a.extend_to(&b)),
            (Some(a), _) => Some(a),
            (_, Some(b)) => Some(b),
            _ => None,
        };

        Source {
            span,
            filepath: self.filepath.clone(),
            path: Path::new(),
            src_module: self.src_module.clone(),
        }
    }

    pub fn respan(&self, span: Span) -> Source {
        Source {
            filepath: self.filepath.clone(),
            span: Some(span),
            path: self.path.clone(),
            src_module: self.src_module.clone(),
        }
    }
}

pub struct Sourced<'a, T>(pub &'a mut T, pub &'a Source);

impl<'a, T> Deref for Sourced<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a, T> DerefMut for Sourced<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a, T> Display for Sourced<'a, T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'a, T> Sourced<'a, T> {
    pub fn unpack(&self) -> (&T, &Source) {
        (self.0, self.1)
    }

    pub fn unpack_mut(&mut self) -> (&mut T, &Source) {
        (self.0, self.1)
    }

    pub fn value(&self) -> &T {
        &self.0
    }

    pub fn value_mut(&mut self) -> &mut T {
        &mut self.0
    }

    pub fn src(&self) -> &Source {
        &self.1
    }

    pub fn src_module(&self) -> &Path {
        &self.1.src_module
    }
}

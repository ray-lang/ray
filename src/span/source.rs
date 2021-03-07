use std::collections::{self, HashMap};

use crate::{
    ast::{Node, Path},
    pathlib::FilePath,
};

use super::Span;

#[derive(Clone, Debug, Default, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Source {
    pub filepath: FilePath,
    pub span: Option<Span>,
    pub path: Path,
    pub src_module: Path,
}

impl std::fmt::Display for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(span) = &self.span {
            write!(f, "{} at {}", self.filepath, span)
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

#[derive(Debug, Clone)]
pub struct SourceMap {
    map: HashMap<u64, Source>,
    docs: HashMap<u64, String>,
}

impl Extend<(u64, Source)> for SourceMap {
    fn extend<T: IntoIterator<Item = (u64, Source)>>(&mut self, iter: T) {
        self.map.extend(iter);
    }
}

impl IntoIterator for SourceMap {
    type Item = (u64, Source);
    type IntoIter = std::collections::hash_map::IntoIter<u64, Source>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}

impl SourceMap {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            docs: HashMap::new(),
        }
    }

    pub fn get<T>(&self, node: &Node<T>) -> Source {
        self.map.get(&node.id).cloned().unwrap()
    }

    pub fn span_of<T>(&self, node: &Node<T>) -> Span {
        self.map.get(&node.id).and_then(|src| src.span).unwrap()
    }

    pub fn respan<T>(&mut self, node: &Node<T>, span: Span) {
        let mut src = self.map.get_mut(&node.id).unwrap();
        src.span = Some(span);
    }

    pub fn filepath_of<T>(&self, node: &Node<T>) -> FilePath {
        self.map
            .get(&node.id)
            .map(|src| src.filepath.clone())
            .unwrap()
    }

    pub fn set_src<T>(&mut self, node: &Node<T>, src: Source) {
        self.map.insert(node.id, src);
    }

    pub fn set_doc<T>(&mut self, node: &Node<T>, doc: String) {
        self.docs.insert(node.id, doc);
    }
}

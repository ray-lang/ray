use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    ops::{Deref, DerefMut},
};

use serde::{Deserialize, Serialize};

use crate::{
    ast::{Decorator, Node, Path, token::TokenKind},
    pathlib::FilePath,
};

use super::Span;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TriviaKind {
    Keyword,
    Comment,
    Operator,
}

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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Trivia {
    pub kind: TriviaKind,
    pub span: Span,
    pub token: Option<TokenKind>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceMap {
    map: HashMap<u64, Source>,
    docs: HashMap<u64, String>,
    decorators: HashMap<u64, Vec<Decorator>>,
    trivia: HashMap<FilePath, Vec<Trivia>>,
    #[serde(default)]
    file_index: HashMap<FilePath, Vec<u64>>,
    #[serde(default)]
    synthetic_nodes: HashSet<u64>,
}

impl Extend<(u64, Source)> for SourceMap {
    fn extend<T: IntoIterator<Item = (u64, Source)>>(&mut self, iter: T) {
        for (id, src) in iter {
            self.set_src_id(id, src);
        }
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
            decorators: HashMap::new(),
            trivia: HashMap::new(),
            file_index: HashMap::new(),
            synthetic_nodes: HashSet::new(),
        }
    }

    pub fn mark_synthetic(&mut self, node_id: u64) {
        self.synthetic_nodes.insert(node_id);
    }

    pub fn is_synthetic(&self, node_id: u64) -> bool {
        self.synthetic_nodes.contains(&node_id)
    }

    pub fn get<T>(&self, node: &Node<T>) -> Source {
        self.map.get(&node.id).cloned().unwrap()
    }

    pub fn get_by_id(&self, id: u64) -> Option<Source> {
        self.map.get(&id).cloned()
    }

    pub fn span_of<T>(&self, node: &Node<T>) -> Span {
        self.map.get(&node.id).and_then(|src| src.span).unwrap()
    }

    pub fn respan<T>(&mut self, node: &Node<T>, span: Span) {
        let src = self.map.get_mut(&node.id).unwrap();
        src.span = Some(span);
    }

    pub fn filepath_of<T>(&self, node: &Node<T>) -> FilePath {
        self.map
            .get(&node.id)
            .map(|src| src.filepath.clone())
            .unwrap()
    }

    fn set_src_id(&mut self, id: u64, src: Source) {
        if let Some(existing) = self.map.insert(id, src.clone()) {
            if !existing.filepath.is_empty() {
                if let Some(ids) = self.file_index.get_mut(&existing.filepath) {
                    ids.retain(|node_id| *node_id != id);
                    if ids.is_empty() {
                        self.file_index.remove(&existing.filepath);
                    }
                }
            }
        }
        if !src.filepath.is_empty() {
            self.file_index
                .entry(src.filepath.clone())
                .or_default()
                .push(id);
        }
    }

    pub fn set_src<T>(&mut self, node: &Node<T>, src: Source) {
        self.set_src_id(node.id, src);
    }

    pub fn set_doc<T>(&mut self, node: &Node<T>, doc: String) {
        self.docs.insert(node.id, doc);
    }

    pub fn doc<T>(&self, node: &Node<T>) -> Option<&String> {
        self.docs.get(&node.id)
    }

    pub fn doc_by_id(&self, id: u64) -> Option<&String> {
        self.docs.get(&id)
    }

    pub fn extend_with(&mut self, mut other: SourceMap) {
        self.docs.extend(other.docs.drain());
        self.decorators.extend(other.decorators.drain());
        for (id, src) in other.map.drain() {
            self.set_src_id(id, src);
        }
        for (filepath, mut entries) in other.trivia.drain() {
            self.trivia
                .entry(filepath)
                .or_default()
                .append(&mut entries);
        }
    }

    pub fn set_decorators<T>(&mut self, node: &Node<T>, decorators: Vec<Decorator>) {
        self.decorators.insert(node.id, decorators);
    }

    pub fn get_decorators<T>(&self, node: &Node<T>) -> Option<&Vec<Decorator>> {
        self.decorators.get(&node.id)
    }

    pub fn has_decorator<T>(&self, node: &Node<T>, p: &Path) -> bool {
        self.decorators
            .get(&node.id)
            .map(|v| v.iter().any(|d| &d.path.value == p))
            .unwrap_or_default()
    }

    pub fn has_inline<T>(&self, node: &Node<T>) -> bool {
        let path = Path::from("inline");
        self.has_decorator(node, &path)
    }

    pub fn record_trivia(
        &mut self,
        filepath: &FilePath,
        kind: TriviaKind,
        span: Span,
        token: Option<TokenKind>,
    ) {
        if span.len() == 0 {
            return;
        }
        self.trivia
            .entry(filepath.clone())
            .or_default()
            .push(Trivia { kind, span, token });
    }

    pub fn trivia_for_file(&self, filepath: &FilePath) -> &[Trivia] {
        self.trivia
            .get(filepath)
            .map(|entries| entries.as_slice())
            .unwrap_or(&[])
    }

    pub fn trivia(&self) -> impl Iterator<Item = (&FilePath, &[Trivia])> {
        self.trivia
            .iter()
            .map(|(filepath, entries)| (filepath, entries.as_slice()))
    }

    pub fn node_ids_for_file(&self, filepath: &FilePath) -> Option<&[u64]> {
        self.file_index.get(filepath).map(|ids| ids.as_slice())
    }

    pub fn find_at_position(
        &self,
        filepath: &FilePath,
        line: usize,
        col: usize,
    ) -> Option<(u64, Source)> {
        let mut best: Option<(u64, Source, usize)> = None;

        for id in self.file_index.get(filepath)?.iter() {
            if self.is_synthetic(*id) {
                continue;
            }

            let Some(src) = self.map.get(id) else {
                continue;
            };

            let Some(span) = src.span.as_ref() else {
                continue;
            };

            if !span.contains_line_col(line, col) {
                continue;
            }

            let span_len = span.len();

            let replace = match &best {
                Some((_, _, best_len)) => span_len <= *best_len,
                None => true,
            };

            if replace {
                best = Some((*id, src.clone(), span_len));
            }
        }

        best.map(|(id, src, _)| (id, src))
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

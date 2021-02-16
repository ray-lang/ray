use crate::ast::{Name, Node, Path, SourceInfo};
use crate::span::Span;

pub struct Import {
    pub path: Node<Path>,
    pub with: Option<Vec<Node<Name>>>,
    pub span: Span,
    pub c_import: Option<(String, Span)>,
}

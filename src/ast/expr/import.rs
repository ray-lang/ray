use crate::ast::{Name, PathNode};
use crate::span::Span;

pub struct Import {
    pub path: PathNode,
    pub with: Option<Vec<Name>>,
    pub span: Span,
    pub c_import: Option<(String, Span)>,
}

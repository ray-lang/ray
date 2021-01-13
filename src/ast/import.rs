use crate::ast::{Name, Path};
use crate::span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Import {
    pub path: Path,
    pub with: Option<Vec<Name>>,
    pub span: Span,
    pub c_import: Option<(String, Span)>,
}

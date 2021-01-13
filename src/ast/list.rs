use crate::ast;
use crate::span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct List {
    pub items: Vec<ast::Expr>,
    pub lbrack_span: Span,
    pub rbrack_span: Span,
}

impl std::fmt::Display for List {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(list [{}])",
            self.items
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

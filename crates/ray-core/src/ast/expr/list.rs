use ray_shared::span::Span;
use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct List {
    pub items: Vec<Node<Expr>>,
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

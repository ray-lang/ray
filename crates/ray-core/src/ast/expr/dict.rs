use ray_shared::span::Span;
use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Dict {
    pub entries: Vec<(Node<Expr>, Node<Expr>)>,
    pub lcurly_span: Span,
    pub rcurly_span: Span,
    pub trailing_comma: bool,
}

impl std::fmt::Display for Dict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let entries = self
            .entries
            .iter()
            .map(|(k, v)| format!("{}: {}", k, v))
            .collect::<Vec<_>>()
            .join(", ");

        if entries.is_empty() {
            write!(f, "(dict {{}})")
        } else if self.trailing_comma {
            write!(f, "(dict {{ {}, }})", entries)
        } else {
            write!(f, "(dict {{ {} }})", entries)
        }
    }
}

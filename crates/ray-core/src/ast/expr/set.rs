use ray_shared::span::Span;
use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Set {
    pub items: Vec<Node<Expr>>,
    pub lcurly_span: Span,
    pub rcurly_span: Span,
    pub trailing_comma: bool,
}

impl std::fmt::Display for Set {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let items = self
            .items
            .iter()
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        if items.is_empty() {
            if self.trailing_comma {
                write!(f, "(set {{,}})")
            } else {
                write!(f, "(set {{}})")
            }
        } else if self.trailing_comma {
            write!(f, "(set {{ {}, }})", items)
        } else {
            write!(f, "(set {{ {} }})", items)
        }
    }
}

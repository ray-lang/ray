use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Sequence {
    pub items: Vec<Node<Expr>>,
    pub trailing: bool, // trailing comma
}

impl Sequence {
    pub fn empty() -> Sequence {
        Sequence {
            items: vec![],
            trailing: false,
        }
    }

    pub fn new(items: Vec<Node<Expr>>) -> Self {
        Sequence {
            items,
            trailing: false,
        }
    }
}

impl std::fmt::Display for Sequence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.items.len() == 0 {
            write!(f, "(seq)")
        } else {
            write!(
                f,
                "(seq {})",
                self.items
                    .iter()
                    .map(|i| i.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    }
}

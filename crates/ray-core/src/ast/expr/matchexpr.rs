use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node, Pattern};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Match {
    pub scrutinee: Box<Node<Expr>>,
    pub arms: Vec<Node<MatchArm>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Node<Pattern>,
    pub body: Box<Node<Expr>>,
}

impl std::fmt::Display for Match {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let arms = self
            .arms
            .iter()
            .map(|a| a.value.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "(match {} {{ {} }})", self.scrutinee, arms)
    }
}

impl std::fmt::Display for MatchArm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} => {})", self.pattern, self.body)
    }
}

use crate::ast::{Expr, Node};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct If {
    pub cond: Box<Node<Expr>>,
    pub then: Box<Node<Expr>>,
    pub els: Option<Box<Node<Expr>>>,
}

impl std::fmt::Display for If {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let els = if let Some(ref els) = self.els {
            format!(" else {}", els)
        } else {
            String::new()
        };
        write!(f, "(if {} {}{})", self.cond, self.then, els,)
    }
}

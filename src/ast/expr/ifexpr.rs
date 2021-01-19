use crate::ast::{Expr, Node};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct If<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub cond: Box<Node<Expr<Info>, Info>>,
    pub then: Box<Node<Expr<Info>, Info>>,
    pub els: Option<Box<Node<Expr<Info>, Info>>>,
}

impl<Info> std::fmt::Display for If<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let els = if let Some(ref els) = self.els {
            format!(" else {}", els)
        } else {
            String::new()
        };
        write!(f, "(if {} {}{})", self.cond, self.then, els,)
    }
}

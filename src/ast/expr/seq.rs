use crate::ast::{Expr, Node};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sequence<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub items: Vec<Node<Expr<Info>, Info>>,
    pub trailing: bool, // trailing comma
}

impl<Info> Sequence<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub fn empty() -> Sequence<Info>
    where
        Info: std::fmt::Debug + Clone + PartialEq + Eq,
    {
        Sequence {
            items: vec![],
            trailing: false,
        }
    }
}

impl<Info> std::fmt::Display for Sequence<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
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

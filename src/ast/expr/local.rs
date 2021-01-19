use crate::ast::{Expr, Node, Pattern, Type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Local<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub is_mut: bool,
    pub pattern: Box<Pattern<Info>>,
    pub ty: Option<Type>,
    pub init: Option<Box<Node<Expr<Info>, Info>>>,
}

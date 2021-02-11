use crate::{
    ast::{Expr, Node, Pattern},
    typing::ty::Ty,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Local<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub is_mut: bool,
    pub pattern: Box<Pattern<Info>>,
    pub ty: Option<Ty>,
    pub init: Option<Box<Node<Expr<Info>, Info>>>,
}

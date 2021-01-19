use crate::{
    ast::{Expr, Node},
    strutils,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub stmts: Vec<Node<Expr<Info>, Info>>,
    pub is_top_level: bool,
}

impl<Info> std::fmt::Display for Block<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.stmts.len() == 0 {
            return write!(f, "(block)");
        }

        let stmts = strutils::indent_lines_iter(&self.stmts, 2);
        write!(f, "(block\n{}\n)", stmts)
    }
}

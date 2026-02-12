use serde::{Deserialize, Serialize};

use crate::{
    ast::{Expr, Node},
    strutils,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Block {
    pub stmts: Vec<Node<Expr>>,
}

impl std::fmt::Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.stmts.len() == 0 {
            return write!(f, "(block)");
        }

        let stmts = strutils::indent_lines_iter(&self.stmts, 2);
        write!(f, "(block\n{}\n)", stmts)
    }
}

impl Block {
    pub fn new(stmts: Vec<Node<Expr>>) -> Self {
        Block { stmts }
    }
}

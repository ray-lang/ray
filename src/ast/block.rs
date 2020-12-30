use crate::strutils;

use super::Expr;

#[derive(Clone, Debug)]
pub struct Block {
    pub stmts: Vec<Expr>,
    pub is_top_level: bool,
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

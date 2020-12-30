use ast::visitor::Visitor;

use crate::ast;
use crate::pathlib::FilePath;
use crate::strutils;

#[derive(Clone, Debug)]
pub struct Module {
    pub path: ast::Path,
    pub stmts: Vec<ast::Expr>,
    pub decls: Vec<ast::Decl>,
    pub imports: Vec<ast::Path>,
    pub submodules: Vec<ast::Path>,
    pub doc_comment: Option<String>,
    pub filepaths: Vec<FilePath>,
}

impl std::fmt::Display for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let decls = strutils::indent_lines_iter(&self.decls, 2);
        let stmts = strutils::indent_lines_iter(&self.stmts, 2);
        if decls.len() != 0 && stmts.len() != 0 {
            write!(f, "(module {}\n{}\n{}\n)", self.path, decls, stmts)
        } else if decls.len() != 0 {
            write!(f, "(module {}\n{}\n)", self.path, decls)
        } else if stmts.len() != 0 {
            write!(f, "(module {}\n{}\n)", self.path, stmts)
        } else {
            write!(f, "(module {})", self.path)
        }
    }
}

impl Module {
    pub fn get_expr(&self, id: ast::Id) -> Option<&ast::Expr> {
        let v = Visitor::new(self);
        for ex in v {
            if ex.id == id {
                return Some(ex);
            }
        }

        None
    }
}

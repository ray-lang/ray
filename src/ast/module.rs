use crate::{
    ast::{Expr, Id, Node, Path},
    pathlib::FilePath,
    strutils,
    typing::{ApplySubst, Subst},
};

use super::HasExpr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module<A, B, Info>
where
    A: std::fmt::Debug + Clone + PartialEq + Eq,
    B: std::fmt::Debug + Clone + PartialEq + Eq,
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub path: Path,
    pub stmts: Vec<Node<A, Info>>,
    pub decls: Vec<Node<B, Info>>,
    pub imports: Vec<Path>,
    pub submodules: Vec<Path>,
    pub doc_comment: Option<String>,
    pub filepaths: Vec<FilePath>,
}

impl<A, B, Info> std::fmt::Display for Module<A, B, Info>
where
    A: std::fmt::Display + std::fmt::Debug + Clone + PartialEq + Eq,
    B: std::fmt::Display + std::fmt::Debug + Clone + PartialEq + Eq,
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
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

impl<A, B, Info> ApplySubst for Module<A, B, Info>
where
    A: std::fmt::Debug + Clone + PartialEq + Eq + ApplySubst,
    B: std::fmt::Debug + Clone + PartialEq + Eq + ApplySubst,
    Info: std::fmt::Debug + Clone + PartialEq + Eq + ApplySubst,
{
    fn apply_subst(self, subst: &Subst) -> Self {
        Module {
            path: self.path,
            stmts: self.stmts.apply_subst(subst),
            decls: self.decls.apply_subst(subst),
            imports: self.imports,
            submodules: self.submodules,
            doc_comment: self.doc_comment,
            filepaths: self.filepaths,
        }
    }
}

impl<A, B, Info> Module<A, B, Info>
where
    A: std::fmt::Debug + Clone + PartialEq + Eq + HasExpr<Info>,
    B: std::fmt::Debug + Clone + PartialEq + Eq,
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub fn get_expr(&self, id: Id) -> Option<&Expr<Info>> {
        todo!()
        // let v = Visitor::from(self);
        // for ex in v {
        //     if ex.id == id {
        //         return Some(ex);
        //     }
        // }

        // None
    }
}

impl<A, B, X> Module<A, B, X>
where
    A: std::fmt::Debug + Clone + PartialEq + Eq,
    B: std::fmt::Debug + Clone + PartialEq + Eq,
    X: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub fn new_from<C, D, Y>(other: &Module<A, B, X>) -> Module<C, D, Y>
    where
        C: std::fmt::Debug + Clone + PartialEq + Eq,
        D: std::fmt::Debug + Clone + PartialEq + Eq,
        Y: std::fmt::Debug + Clone + PartialEq + Eq,
    {
        Module {
            path: other.path.clone(),
            stmts: vec![],
            decls: vec![],
            imports: other.imports.clone(),
            submodules: other.submodules.clone(),
            doc_comment: other.doc_comment.clone(),
            filepaths: other.filepaths.clone(),
        }
    }
}

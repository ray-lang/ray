use crate::{
    ast::{Node, Path},
    pathlib::FilePath,
    strutils,
    typing::{state::TyEnv, ApplySubst, Subst},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module<A, B>
where
    A: std::fmt::Debug + Clone + PartialEq + Eq,
    B: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub path: Path,
    pub stmts: Vec<Node<A>>,
    pub decls: Vec<Node<B>>,
    pub imports: Vec<Path>,
    pub submodules: Vec<Path>,
    pub defs: TyEnv,
    pub doc_comment: Option<String>,
    pub root_filepath: FilePath,
    pub filepaths: Vec<FilePath>,
    pub is_lib: bool,
}

impl<A, B> std::fmt::Display for Module<A, B>
where
    A: std::fmt::Display + std::fmt::Debug + Clone + PartialEq + Eq,
    B: std::fmt::Display + std::fmt::Debug + Clone + PartialEq + Eq,
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

impl<A, B> ApplySubst for Module<A, B>
where
    A: std::fmt::Debug + Clone + PartialEq + Eq + ApplySubst,
    B: std::fmt::Debug + Clone + PartialEq + Eq + ApplySubst,
{
    fn apply_subst(self, subst: &Subst) -> Self {
        Module {
            path: self.path,
            stmts: self.stmts.apply_subst(subst),
            decls: self.decls.apply_subst(subst),
            imports: self.imports,
            submodules: self.submodules,
            defs: self.defs,
            doc_comment: self.doc_comment,
            root_filepath: self.root_filepath,
            filepaths: self.filepaths,
            is_lib: self.is_lib,
        }
    }
}

impl<A, B> Module<A, B>
where
    A: std::fmt::Debug + Clone + PartialEq + Eq,
    B: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub fn new_from(other: &Module<A, B>) -> Module<A, B> {
        Module {
            path: other.path.clone(),
            stmts: vec![],
            decls: vec![],
            imports: other.imports.clone(),
            submodules: other.submodules.clone(),
            defs: other.defs.clone(),
            doc_comment: other.doc_comment.clone(),
            root_filepath: other.root_filepath.clone(),
            filepaths: other.filepaths.clone(),
            is_lib: other.is_lib,
        }
    }
}

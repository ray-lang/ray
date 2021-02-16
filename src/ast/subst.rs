use crate::{
    hir::HirInfo,
    typing::{
        collect::{CollectConstraints, CollectDeclarations},
        ApplySubst, Subst,
    },
};

use super::{Decl, Expr, Module, Node};

impl ApplySubst for Expr {
    fn apply_subst(self, subst: &Subst) -> Self {
        todo!()
    }
}

impl ApplySubst for Decl {
    fn apply_subst(self, subst: &Subst) -> Self {
        todo!()
    }
}

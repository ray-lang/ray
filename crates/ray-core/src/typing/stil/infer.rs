use std::{collections::HashMap, ops::Deref};

use crate::{
    ast::{self, Decl, Expr, Module, Node},
    errors::RayError,
    span::Source,
    typing::{
        ApplySubstMut, Subst, TyCtx,
        assumptions::AssumptionSet,
        predicate::TyPredicate,
        stil::{GetDecls, VerifyTys},
        ty::Ty,
    },
};

use super::context::InferCtx;

pub trait SimpleTypeInfer {
    type Output;

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output;
}

impl<T> SimpleTypeInfer for Vec<T>
where
    T: SimpleTypeInfer<Output = (Option<Ty>, Option<Vec<TyPredicate>>, AssumptionSet)>,
{
    type Output = (Vec<TyPredicate>, AssumptionSet);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        let mut preds = vec![];
        let mut aset = aset.clone();
        for el in self.iter() {
            let (_, el_preds, el_aset) = el.simple_ty_infer(&aset, icx);
            if let Some(el_preds) = el_preds {
                preds.extend(el_preds);
            }
            aset.extend(el_aset);
        }
        (preds, aset)
    }
}

impl SimpleTypeInfer for Module<(), Decl> {
    type Output = Result<AssumptionSet, RayError>;

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        // create an assumption set with the explicitly typed declarations
        let (explicits, implicits): (Vec<_>, Vec<_>) = self
            .decls
            .iter()
            .flat_map(|d| d.get_decls())
            .partition(|decl| decl.is_typed());

        let explicits_aset = explicits
            .iter()
            .flat_map(|d| d.get_defs())
            .filter_map(|(path, maybe_ty)| maybe_ty.map(|ty| (path.clone(), ty.clone())))
            .collect::<AssumptionSet>();

        let mut aset = aset.clone();
        aset.extend(explicits_aset.clone());

        // infer types of implicitly typed declarations
        let (mut preds, implicits_aset) = implicits.simple_ty_infer(&aset, icx);
        aset.extend(implicits_aset.clone());

        // verify types of explicitly typed declarations
        let explicits_preds = explicits.verify_tys(&aset, icx)?;
        preds.extend(explicits_preds);
        preds.apply_subst_mut(icx.subst());
        icx.reduce_preds(&mut preds);

        let preds_subst = icx.default_subst(&vec![], &preds)?;
        icx.subst_mut().extend(preds_subst);

        let mut aset = explicits_aset;
        aset.extend(implicits_aset);
        aset.apply_subst_mut(icx.subst());
        Ok(aset)
    }
}

impl SimpleTypeInfer for Node<ast::Pattern> {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for Node<Expr> {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::asm::Asm, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::BinOp, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Block, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Call, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Cast, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Curly, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Dot, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Func, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::For, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::If, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::List, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Literal, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Name, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::New, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Pattern, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Path, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Range, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Tuple, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::UnaryOp, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::While, &Source) {
    type Output = (Option<Ty>, Vec<AssumptionSet>);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

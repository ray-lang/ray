use std::ops::Deref;

use itertools::Itertools;

use crate::{
    ast::{self, Decl, Node},
    errors::{RayError, RayErrorKind},
    span::Source,
    typing::{
        assumptions::AssumptionSet, predicate::TyPredicate, traits::CollectTyVars, ty::Ty,
        ApplySubstMut,
    },
    utils::DrainInPlace,
};

use super::{context::InferCtx, SimpleTypeInfer};

pub trait GetDecls {
    fn get_decls(&self) -> Vec<Node<&Decl>>;
}

impl<D> GetDecls for Vec<D>
where
    D: GetDecls,
{
    fn get_decls(&self) -> Vec<Node<&Decl>> {
        self.into_iter().map(|decl| decl.get_decls()).concat()
    }
}

impl GetDecls for Node<Decl> {
    fn get_decls(&self) -> Vec<Node<&Decl>> {
        let mut decls = vec![];
        match self.deref() {
            Decl::Extern(ex) => {
                decls.extend(ex.decl_node().get_decls());
            }
            Decl::Mutable(_) => todo!(),
            Decl::Name(_) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::Func(_) | Decl::FnSig(_) => {
                decls.push(self.as_ref());
            }
            Decl::Struct(_) => todo!(),
            Decl::Trait(tr) => {
                decls.extend(tr.funcs.get_decls());
            }
            Decl::TypeAlias(_, _) => todo!(),
            Decl::Impl(im) => {
                if let Some(externs) = &im.externs {
                    decls.extend(externs.get_decls());
                }

                if let Some(funcs) = &im.funcs {
                    decls.extend(funcs.get_decls());
                }

                if let Some(consts) = &im.consts {
                    todo!();
                    // decls.extend(
                    //     consts
                    //         .iter()
                    //         .flat_map(|d| d.lhs.path().map(|path| (path, None))),
                    // );
                }
            }
        }
        decls
    }
}

pub trait VerifyTys {
    type Output;

    fn verify_tys(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output;
}

impl VerifyTys for Vec<Node<&Decl>> {
    type Output = Result<Vec<TyPredicate>, RayError>;

    fn verify_tys(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        let mut all_preds = vec![];
        let mut errs = vec![];
        for decl in self.iter() {
            let ty = unless!(decl.get_ty(), else {
                let src = icx.srcmap().get(decl);
                errs.push(RayError {
                    msg: format!("{} does not have a type", decl.desc()),
                    src: vec![src],
                    kind: RayErrorKind::Type,
                });
                continue;
            });

            let (_, preds, aset) = decl.simple_ty_infer(aset, icx);

            let mut inst_ty = icx.fresh_inst(ty);
            let mut aset = aset.clone();
            let subst = icx.subst();
            inst_ty.apply_subst_mut(subst);
            aset.apply_subst_mut(subst);

            let fixed_vars = aset.collect_tyvars();
            let mut quant_vars = inst_ty.collect_tyvars();
            quant_vars.drain_in_place(|v| fixed_vars.contains(v));
            inst_ty = inst_ty.quantify(quant_vars.clone());

            if let (Some(inst_preds), Some(preds)) = (inst_ty.qualifiers(), preds) {
                let preds = preds
                    .into_iter()
                    .filter(|pred| icx.entails_pred(inst_preds.iter(), pred))
                    .collect();

                let (deferred_preds, retained_preds) = match icx
                    .split_preds(fixed_vars, quant_vars, preds)
                    .map_err(|mut err| {
                        let src = icx.srcmap().get(decl);
                        err.src.push(src);
                        err
                    }) {
                    Ok((ds, rs)) => (ds, rs),
                    Err(err) => {
                        errs.push(err);
                        continue;
                    }
                };

                if ty != &inst_ty {
                    let src = icx.srcmap().get(decl);
                    errs.push(RayError {
                        msg: str!("signature too general"),
                        src: vec![src],
                        kind: RayErrorKind::Type,
                    });
                    continue;
                }

                if retained_preds.len() != 0 {
                    let src = icx.srcmap().get(decl);
                    errs.push(RayError {
                        msg: str!("context too weak"),
                        src: vec![src],
                        kind: RayErrorKind::Type,
                    });
                    continue;
                }

                all_preds.extend(deferred_preds);
            }
        }

        Ok(all_preds)
    }
}

impl SimpleTypeInfer for Node<&Decl> {
    type Output = (Option<Ty>, Option<Vec<TyPredicate>>, AssumptionSet);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        let src = icx.srcmap().get(self);
        match self.deref() {
            Decl::Extern(ext) => (ext, &src).simple_ty_infer(aset, icx),
            Decl::Mutable(mt) => todo!(),
            Decl::Name(n) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::Func(_) => todo!(),
            Decl::FnSig(_) => todo!(),
            Decl::Struct(_) => todo!(),
            Decl::Trait(_) => todo!(),
            Decl::TypeAlias(_, _) => todo!(),
            Decl::Impl(_) => todo!(),
        }
    }
}

impl SimpleTypeInfer for (&ast::Func, &Source, Option<&Ty>) {
    type Output = (Option<Ty>, Option<Vec<TyPredicate>>, AssumptionSet);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

impl SimpleTypeInfer for (&ast::Extern, &Source) {
    type Output = (Option<Ty>, Option<Vec<TyPredicate>>, AssumptionSet);

    fn simple_ty_infer(&self, aset: &AssumptionSet, icx: &mut InferCtx) -> Self::Output {
        todo!()
    }
}

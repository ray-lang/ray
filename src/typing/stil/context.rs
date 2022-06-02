use std::ops::Deref;

use itertools::Itertools;

use crate::{
    ast::{self, Decl, Expr, Module, Node},
    errors::{RayError, RayErrorKind},
    span::{Source, SourceMap},
    typing::{
        assumptions::AssumptionSet,
        predicate::TyPredicate,
        traits::CollectTyVars,
        ty::{Ty, TyVar},
        ApplySubst, Subst, TyCtx,
    },
    utils::DrainInPlace,
};

use super::{ambiguity::Ambiguity, tymatch::TyMatch};

pub struct InferCtx<'a> {
    tcx: &'a mut TyCtx,
    srcmap: &'a SourceMap,
    subst: Subst,
    defaults: Vec<Ty>,
}

impl<'a> InferCtx<'a> {
    pub fn new(tcx: &'a mut TyCtx, srcmap: &'a SourceMap) -> Self {
        Self {
            tcx,
            srcmap,
            subst: Subst::new(),
            defaults: vec![Ty::int(), Ty::float()],
        }
    }

    pub fn subst(&self) -> &Subst {
        &self.subst
    }

    pub fn subst_mut(&mut self) -> &mut Subst {
        &mut self.subst
    }

    pub fn srcmap(&self) -> &SourceMap {
        &self.srcmap
    }

    pub fn fresh_inst(&self, ty: &Ty) -> Ty {
        todo!()
    }

    pub fn reduce_preds(&self, preds: &mut Vec<TyPredicate>) {
        self.to_hnf(preds);
        self.simplify_preds(preds);
    }

    pub fn default_subst(
        &self,
        vars: &Vec<TyVar>,
        preds: &Vec<TyPredicate>,
    ) -> Result<Subst, RayError> {
        self.with_defaults(
            |ambs, tys| {
                ambs.iter()
                    .map(|a| a.ty_var().clone())
                    .zip(tys.clone())
                    .collect::<Subst>()
            },
            vars,
            preds,
        )
    }

    pub fn defaulted_preds(
        &self,
        vars: &Vec<TyVar>,
        preds: &Vec<TyPredicate>,
    ) -> Result<Vec<TyPredicate>, RayError> {
        self.with_defaults(
            |ambs, _| ambs.iter().flat_map(|amb| amb.preds().clone()).collect(),
            vars,
            preds,
        )
    }

    pub fn with_defaults<F, T>(
        &self,
        f: F,
        vars: &Vec<TyVar>,
        preds: &Vec<TyPredicate>,
    ) -> Result<T, RayError>
    where
        F: Fn(&Vec<Ambiguity>, &Vec<Ty>) -> T,
    {
        let ambiguities = self.get_ambiguities(vars, preds);
        let tys = ambiguities
            .iter()
            .map(|amb| self.get_candidates(amb))
            .collect::<Vec<_>>();

        if tys.len() == 0 || tys.iter().any(|a| a.len() == 0) {
            return Err(RayError {
                msg: str!("cannot resolve ambiguity"),
                src: vec![],
                kind: RayErrorKind::Type,
            });
        }

        Ok(f(&ambiguities, &tys[0]))
    }

    pub fn entails_pred<'p, P>(&self, preds: P, pred: &TyPredicate) -> bool
    where
        P: Clone + Iterator<Item = &'p TyPredicate>,
    {
        preds
            .clone()
            .any(|q| self.entailed_by_super(q).contains(pred))
            || self
                .entailed_by_inst(pred)
                .map(|qs| qs.iter().all(|q| self.entails_pred(preds.clone(), q)))
                .unwrap_or_default()
    }

    pub fn split_preds(
        &self,
        fixed_vars: Vec<TyVar>,
        quant_vars: Vec<TyVar>,
        mut preds: Vec<TyPredicate>,
    ) -> Result<(Vec<TyPredicate>, Vec<TyPredicate>), RayError> {
        self.reduce_preds(&mut preds);
        let (deferred_preds, mut retained_preds): (Vec<_>, Vec<_>) =
            preds.into_iter().partition(|pred| {
                pred.collect_tyvars()
                    .into_iter()
                    .all(|v| fixed_vars.contains(&v))
            });

        let mut vars = fixed_vars;
        vars.extend(quant_vars);
        let default_preds = self.defaulted_preds(&vars, &retained_preds)?;
        retained_preds.drain_in_place(|pred| default_preds.contains(pred));
        Ok((deferred_preds, retained_preds))
    }

    fn get_ambiguities(&self, vars: &Vec<TyVar>, preds: &Vec<TyPredicate>) -> Vec<Ambiguity> {
        let pred_tyvars = preds.collect_tyvars();
        pred_tyvars
            .iter()
            .filter(|v| !vars.contains(v))
            .cloned()
            .map(|ty_var| {
                let preds = preds
                    .iter()
                    .filter(|p| p.collect_tyvars().contains(&ty_var))
                    .cloned()
                    .collect();
                Ambiguity::new(ty_var, preds)
            })
            .collect()
    }

    fn get_candidates(&self, amb: &Ambiguity) -> Vec<Ty> {
        self.defaults
            .iter()
            .filter(|&ty| {
                amb.preds()
                    .iter()
                    .map(|pred| match pred {
                        TyPredicate::Trait(trait_ty) => {
                            let mut trait_ty = trait_ty.clone();
                            trait_ty.set_ty_param_at(0, ty.clone());
                            TyPredicate::Trait(trait_ty)
                        }
                        TyPredicate::Literal(_, _) => todo!(),
                        TyPredicate::HasMember(_, _, _) => todo!(),
                    })
                    .all(|pred| self.entails_pred(std::iter::empty(), &pred))
            })
            .cloned()
            .collect()
    }

    fn to_hnf(&self, preds: &mut Vec<TyPredicate>) {
        let old_preds = preds.drain(..).collect::<Vec<_>>();
        for pred in old_preds {
            if pred.in_hnf() {
                preds.push(pred);
                continue;
            }

            if let Some(mut more_preds) = self.entailed_by_inst(&pred) {
                self.to_hnf(&mut more_preds);
                preds.extend(more_preds);
            }
        }
    }

    fn simplify_preds(&self, preds: &mut Vec<TyPredicate>) {
        let mut idx = 0;
        while idx < preds.len() {
            let pred = &preds[idx];
            if self.entails_pred((&preds[0..idx]).iter().chain(&preds[idx + 1..]), pred) {
                preds.remove(idx);
                continue;
            }

            idx += 1;
        }
    }

    fn entailed_by_inst(&self, pred: &TyPredicate) -> Option<Vec<TyPredicate>> {
        let trait_ty = match pred {
            TyPredicate::Trait(trait_ty) => trait_ty,
            TyPredicate::Literal(_, _) | TyPredicate::HasMember(_, _, _) => todo!(),
        };

        let impls = unless!(self.tcx.get_impls(trait_ty), else return None);
        for i in impls {
            if let Ok(preds) = i
                .base_ty
                .match_tys(trait_ty)
                .map(|sub| i.predicates.clone().apply_subst(&sub))
            {
                return Some(preds);
            }
        }

        None
    }

    fn entailed_by_super(&self, pred: &TyPredicate) -> Vec<TyPredicate> {
        let mut preds = vec![pred.clone()];
        let trait_ty = match pred {
            TyPredicate::Trait(trait_ty) => trait_ty,
            TyPredicate::Literal(_, _) | TyPredicate::HasMember(_, _, _) => return preds,
        };

        let supers = unless!(
            self.tcx.get_super_traits_from_ty(trait_ty),
            else return preds
        );

        for super_ty in supers {
            let super_base_ty = super_ty.first_ty_param();
            let mut trait_ty = trait_ty.clone();
            trait_ty.set_ty_param_at(0, super_base_ty.clone());
            // note: we're only handling traits here because the other predicate
            // types cannot be entailed this way
            let pred = TyPredicate::Trait(trait_ty);
            preds.extend(self.entailed_by_super(&pred));
        }

        preds
    }
}

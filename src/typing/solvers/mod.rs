mod greedy;

pub use greedy::*;

use std::collections::{HashMap, HashSet};

use crate::{
    typing::{
        predicate::TyPredicate,
        ty::{LiteralKind, Ty, TyVar},
        ApplySubst, Ctx, InferError, Subst,
    },
    utils::join,
};

use super::{
    constraints::{
        AssumeConstraint, Constraint, ConstraintKind, EqConstraint, GenConstraint, InstConstraint,
        ProveConstraint, Satisfiable,
    },
    traits::{
        HasBasic, HasPredicates, HasState, HasSubst, Instantiate, PolymorphismInfo, QualifyTypes,
        QuantifyTypes, Skolemize,
    },
    ApplySubstMut,
};

#[derive(Clone, PartialEq, Eq)]
pub struct Solution {
    pub subst: Subst,
    pub ty_map: Subst,
    pub inst_map: Subst,
    pub preds: Vec<TyPredicate>,
}

impl std::fmt::Debug for Solution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Solution")
            .field("subst", &self.subst)
            .field("ty_map", &self.ty_map)
            .field("inst_map", &self.inst_map)
            .field("preds", &self.preds)
            .finish()
    }
}

impl ApplySubst for Solution {
    fn apply_subst(mut self, subst: &Subst) -> Self {
        self.subst = self.subst.apply_subst(&subst);
        self.ty_map = self.ty_map.apply_subst(&self.subst);
        self.inst_map = self.inst_map.apply_subst(&self.subst);
        self.preds = self.preds.apply_subst(&self.subst);
        self.preds.sort();
        self.preds.dedup();
        self
    }
}

impl Solution {
    pub fn satisfies(&self, constraints: Vec<Constraint>, ctx: &Ctx) -> Vec<InferError> {
        let mut errs = vec![];
        for c in constraints.into_iter().rev() {
            if let Some(e) = self.satisfies_constraint(c, ctx).err() {
                errs.push(e);
            }
        }

        errs
    }

    fn satisfies_constraint(&self, c: Constraint, ctx: &Ctx) -> Result<(), InferError> {
        c.satisfied_by(self, ctx)
    }

    pub fn formalize_types(&mut self) {
        // formalize any unbound type variables
        for ty in self.ty_map.values() {
            let ty: Ty = ty.clone().apply_subst(&self.subst);
            if ty.is_func() {
                let subst = ty.formalize();
                self.subst.extend(subst);
            } else if let Ty::All(_, t) = ty {
                let mut subst = Subst::new();
                let (preds, ty) = t.unpack_qualified_ty();
                for p in preds {
                    if let Ty::Var(v) = &ty {
                        if p.is_int_trait() {
                            subst.insert(v.clone(), Ty::int());
                            break;
                        } else if p.is_float_trait() {
                            subst.insert(v.clone(), Ty::float());
                            break;
                        }
                    }
                }
                self.subst.extend(subst);
            }
        }
    }

    pub fn get_ty(&self, r: Ty) -> Result<Ty, InferError> {
        Ok(if let Ty::Var(v) = r {
            let r = self.ty_map.get(&v);
            if r.is_none() {
                return Err(InferError {
                    msg: format!("type variable `{}` cannot be solved", v),
                    src: vec![],
                });
            }

            r.unwrap().clone()
        } else {
            r
        })
    }

    pub fn get_var(&self, v: TyVar) -> Result<Ty, InferError> {
        if let Some(s) = self.subst.get(&v) {
            Ok(s.clone())
        } else {
            Err(InferError {
                msg: format!("type variable `{}` cannot be solved", v),
                src: vec![],
            })
        }
    }
}

pub trait Solver: HasBasic + HasSubst + HasState + HasPredicates {
    fn solution(self) -> Solution;

    fn solve(mut self) -> (Solution, Vec<Constraint>)
    where
        Self: std::marker::Sized,
    {
        // first solve the constraints
        let mut check = vec![];
        self.solve_constraints(&mut check);

        // then if there are any literal predicates that have type variables add
        // equality constraints that unify with the default type of the literal
        let mut cs = vec![];
        for (pred, info) in self.get_preds() {
            if let TyPredicate::Trait(t) = pred {
                match t {
                    Ty::Projection(x, p, _) => {
                        if x == "core::Int" || x == "core::Float" {
                            let base_ty = p[0].clone();
                            if base_ty.is_tyvar() {
                                cs.push(
                                    EqConstraint::new(
                                        p[0].clone(),
                                        if x == "core::Int" {
                                            Ty::int()
                                        } else {
                                            Ty::float()
                                        },
                                    )
                                    .with_info(info.clone()),
                                );
                            }
                        }
                    }
                    _ => continue,
                }
            }
        }

        self.add_constraints(cs);
        self.solve_constraints(&mut check);

        let mut solution = self.solution();
        let mut check = check.apply_subst(&solution.subst);
        check.qualify_tys(&solution.preds);
        check.quantify_tys();

        solution.formalize_types();

        let subst = solution.subst.clone();
        solution = solution.apply_subst(&subst);

        check = check.apply_subst(&solution.subst);

        log::debug!("------------- After formalization ---------------");
        log::debug!("constraints to check: {:#?}", check);
        log::debug!("solution: {:#?}", solution);

        (solution, check)
    }

    fn solve_constraints(&mut self, check: &mut Vec<Constraint>) {
        while let Some(c) = self.pop_constraint() {
            self.solve_constraint(c, check);
            self.apply_subst();
        }
    }

    fn solve_constraint(&mut self, c: Constraint, check: &mut Vec<Constraint>) {
        log::debug!("solve {:?}", c);
        let c_clone = c.clone();
        let info = c.info;
        match c.kind {
            ConstraintKind::Eq(c) => {
                let (s, t) = c.unpack();
                if self.unify_terms(&s, &t, &info) {
                    return;
                }
            }
            ConstraintKind::Gen(c) => {
                let (m, v, t) = c.unpack();
                self.make_consistent();
                let m = m.apply_subst(self.get_subst());
                let t = t.apply_subst(self.get_subst());
                let s = self.generalize_with_preds(&m, t);
                self.store_ty(v, s, info);
            }
            ConstraintKind::Inst(c) => {
                let (t, r) = c.unpack();
                let s = self.find_ty(&r);
                self.inst_ty(t.clone(), s.clone());
                let info = info.inst_ty(&s);
                let t_sub = s.instantiate(&mut self.get_tf());
                let (p, t_sub) = t_sub.unpack_qualified_ty();
                for pred in p {
                    self.add_constraint(ProveConstraint::new(pred).with_info(info.clone()))
                }

                self.add_constraint(EqConstraint::new(t, t_sub).with_info(info));
            }
            ConstraintKind::Skol(c) => {
                let (monos, t, r) = c.unpack();
                let s = self.find_ty(&r);
                let (t_sub, skolems) = s.skolemize(&mut self.get_sf());
                let info = info.skol_ty(&s);
                self.add_skolems(&info, skolems, monos);

                let (p, t_sub) = t_sub.unpack_qualified_ty();
                for pred in p {
                    self.add_constraint(AssumeConstraint::new(pred).with_info(info.clone()))
                }
                self.add_constraint(EqConstraint::new(t, t_sub).with_info(info));
            }
            ConstraintKind::Implicit(c) => {
                let (tyvars, t1, t2) = c.unpack();
                let sv = self.new_svar();

                self.add_constraints(vec![
                    InstConstraint::new(t1, Ty::Var(sv.clone())).with_info(info.clone()),
                    GenConstraint::new(
                        tyvars.into_iter().map(|tv| Ty::Var(tv.clone())).collect(),
                        sv,
                        t2,
                    )
                    .with_info(info),
                ]);
            }
            ConstraintKind::Default(c) => {
                let (ty, default_ty) = c.unpack();
                if let Ty::Var(_) = self.get_var(&ty) {
                    // unify terms if `ty` has still not been unified
                    if self.unify_terms(&ty, &default_ty, &info) {
                        return;
                    }
                }
            }
            ConstraintKind::Prove(c) => self.prove_pred(c.get_predicate(), info),
            ConstraintKind::Assume(c) => self.assume_pred(c.get_predicate(), info),
        }

        check.push(c_clone);
    }
}

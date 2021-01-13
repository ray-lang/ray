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
    traits::{HasBasic, HasPredicates, HasState, HasSubst, PolymorphismInfo, Skolemize},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Solution {
    pub subst: Subst,
    pub ty_map: Subst,
    pub preds: Vec<TyPredicate>,
}

impl Solution {
    pub fn satisfies(&self, constraints: Vec<Constraint>, ctx: &Ctx) -> Vec<InferError> {
        let mut errs = vec![];
        println!("satisfies? = {:?}", constraints);
        for c in constraints.into_iter().rev() {
            if let Some(e) = self.satisfies_constraint(c, ctx).err() {
                errs.push(e);
            }
        }

        errs
    }

    fn satisfies_constraint(&self, c: Constraint, ctx: &Ctx) -> Result<(), InferError> {
        println!("apply_subst - before: {:?}", c);
        let c = c.apply_subst(&self.subst);
        println!("apply_subst - after: {:?}", c);
        c.satisfied_by(self, ctx)
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
            if let TyPredicate::Literal(t, k) = pred {
                if t.is_tyvar() {
                    cs.push(
                        EqConstraint::new(
                            t.clone(),
                            match k {
                                LiteralKind::Int => Ty::int(),
                                LiteralKind::Float => Ty::float(),
                            },
                        )
                        .with_info(info.clone()),
                    );
                }
            }
        }

        self.add_constraints(cs);
        self.solve_constraints(&mut check);
        // self.check_skolems();

        (self.solution(), check)
    }

    fn solve_constraints(&mut self, check: &mut Vec<Constraint>) {
        while let Some(c) = self.pop_constraint() {
            println!("solving constraint: {:?}", c);
            self.solve_constraint(c, check);
            self.apply_subst();
        }
    }

    fn solve_constraint(&mut self, c: Constraint, check: &mut Vec<Constraint>) {
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
                self.ctx_reduce();
                let m = m.apply_subst(self.get_subst());
                let t = t.apply_subst(self.get_subst());
                println!("generalize (before): {}", t);
                let s = self.generalize_with_preds(&m, t);
                println!("generalize (after): {}", s);
                self.store_ty(v, s, info);
            }
            ConstraintKind::Inst(c) => {
                let (t, r) = c.unpack();
                let s = self.find_ty(&r);
                let info = info.inst_ty(&s);
                println!("instantiate (before): {}", s);
                let t_sub = s.instantiate(&mut self.get_tf());
                println!("instantiate (after): {}", t_sub);
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
                println!("t_sub = {}", t_sub);
                println!("skolems = {}", join(&skolems, ", "));
                let info = info.skol_ty(&s);
                self.add_skolems(&info, skolems, monos);

                let (p, t_sub) = t_sub.unpack_qualified_ty();
                for pred in p {
                    println!("add assume constraint: {:?}", pred);
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
            ConstraintKind::Prove(c) => self.prove_pred(c.get_predicate(), info),
            ConstraintKind::Assume(c) => self.assume_pred(c.get_predicate(), info),
        }

        check.push(c_clone);
    }
}

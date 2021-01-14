use std::{
    cell::RefMut,
    collections::{HashMap, HashSet, VecDeque},
};

use crate::typing::{
    predicate::TyPredicate,
    top::{
        constraints::EqConstraint,
        state::TyVarFactory,
        traits::{Generalize, HasFreeVars, HasPredicates},
    },
    ty::{Ty, TyVar},
    ApplySubst, Ctx, Subst,
};

use crate::typing::top::{
    constraints::{Constraint, ConstraintInfo},
    traits::{HasBasic, HasState, HasSubst},
};

use super::{Solution, Solver};

#[derive(Debug)]
pub struct GreedySolver<'a> {
    ctx: &'a mut Ctx,
    subst: Subst,
    skolems: Vec<(Vec<TyVar>, Vec<TyVar>, ConstraintInfo)>,
    assume_preds: Vec<(TyPredicate, ConstraintInfo)>,
    prove_preds: Vec<(TyPredicate, ConstraintInfo)>,
    generalized_preds: Vec<(TyPredicate, ConstraintInfo)>,
    constraints: VecDeque<Constraint>,
    ty_map: HashMap<TyVar, (Ty, ConstraintInfo)>,
}

impl<'a> GreedySolver<'a> {
    pub fn new(constraints: Vec<Constraint>, ctx: &'a mut Ctx) -> GreedySolver<'a> {
        GreedySolver {
            ctx,
            constraints: constraints.into(),
            subst: Subst::new(),
            skolems: vec![],
            assume_preds: vec![],
            prove_preds: vec![],
            generalized_preds: vec![],
            ty_map: HashMap::new(),
        }
    }
}

impl<'a> Solver for GreedySolver<'a> {
    fn solution(self) -> Solution {
        let GreedySolver {
            subst,
            assume_preds,
            prove_preds,
            generalized_preds,
            ty_map,
            ..
        } = self;

        // collect the type map of generalized types
        let ty_map = ty_map.into_iter().map(|(v, (t, _))| (v, t)).collect();

        // collect and dedup all of the predicates
        let mut preds = prove_preds
            .into_iter()
            .chain(assume_preds.into_iter())
            .chain(generalized_preds.into_iter())
            .map(|(p, _)| p.apply_subst(&subst))
            .collect::<Vec<_>>();
        preds.dedup();

        Solution {
            subst,
            ty_map,
            preds,
        }
    }
}

impl<'a> HasBasic for GreedySolver<'a> {
    fn get_constraints(&self) -> Vec<Constraint> {
        self.constraints.clone().into()
    }

    fn add_constraint(&mut self, c: Constraint) {
        self.constraints.push_front(c);
    }

    fn add_constraints(&mut self, cs: Vec<Constraint>) {
        for c in cs {
            self.add_constraint(c);
        }
    }

    fn pop_constraint(&mut self) -> Option<Constraint> {
        self.constraints.pop_front()
    }

    fn add_error(&mut self, _: ConstraintInfo) {
        todo!()
    }

    fn get_errors(&self) -> Vec<ConstraintInfo> {
        todo!()
    }
}

impl<'a> HasSubst for GreedySolver<'a> {
    fn apply_subst(&mut self) {
        let constraints = std::mem::take(&mut self.constraints);
        let prove_preds = std::mem::take(&mut self.prove_preds);
        let assume_preds = std::mem::take(&mut self.assume_preds);
        let generalized_preds = std::mem::take(&mut self.generalized_preds);
        self.prove_preds = prove_preds
            .into_iter()
            .map(|(p, i)| (p.apply_subst(&self.subst), i))
            .collect();
        self.assume_preds = assume_preds
            .into_iter()
            .map(|(p, i)| (p.apply_subst(&self.subst), i))
            .collect();
        self.generalized_preds = generalized_preds
            .into_iter()
            .map(|(p, i)| (p.apply_subst(&self.subst), i))
            .collect();
        self.constraints = constraints.apply_subst(&self.subst);
    }

    fn get_subst(&self) -> &Subst {
        &self.subst
    }

    fn unify_terms(&mut self, a: &Ty, b: &Ty, info: &ConstraintInfo) -> bool {
        let cs = match a.unify_with(
            b,
            |sub| {
                let mut new_sub = self.subst.clone();
                new_sub.union_inplace(sub, |x, y| {
                    self.unify_terms(x, y, info);
                });
                self.subst = new_sub;
            },
            |x, y| EqConstraint::new(x.clone(), y.clone()).with_info(info.clone()),
        ) {
            Ok((_, cs)) => cs,
            _ => return false,
        };

        let added = cs.len() != 0;
        for c in cs {
            self.add_constraint(c);
        }
        added

        // match (a, b) {
        //     (Ty::Literal(LiteralKind::Int, v), t) | (t, Ty::Literal(LiteralKind::Int, v))
        //         if t.is_int_ty() =>
        //     {
        //         let mut added_constraints = false;
        //         let mut sub = self.subst.clone();
        //         sub.union_inplace(subst! { v.clone() => t.clone() }, |x, y| {
        //             added_constraints = added_constraints || self.unify_terms(x, y, info);
        //         });
        //         self.subst = sub;
        //         added_constraints
        //     }
        //     (Ty::Literal(LiteralKind::Float, v), t) | (t, Ty::Literal(LiteralKind::Float, v))
        //         if t.is_float_ty() =>
        //     {
        //         let mut added_constraints = false;
        //         let mut sub = self.subst.clone();
        //         sub.union_inplace(subst! { v.clone() => t.clone() }, |x, y| {
        //             added_constraints = added_constraints || self.unify_terms(x, y, info);
        //         });
        //         self.subst = sub;
        //         added_constraints
        //     }
        //     (Ty::Var(tv), t) | (t, Ty::Var(tv)) if a != b => {
        //         let mut added_constraints = false;
        //         if !t.free_vars().contains(&tv) {
        //             let mut sub = self.subst.clone();
        //             sub.union_inplace(subst! { tv.clone() => t.clone() }, |x, y| {
        //                 added_constraints = added_constraints || self.unify_terms(x, y, info);
        //             });
        //             self.subst = sub;
        //         }
        //         added_constraints
        //     }
        //     (Ty::Projection(a, s), Ty::Projection(b, t)) if a == b => {
        //         let mut added_constraints = false;
        //         for (x, y) in s.iter().zip(t.iter()).rev() {
        //             self.add_constraint(
        //                 EqConstraint::new(x.clone(), y.clone()).with_info(info.clone()),
        //             );
        //             added_constraints = true;
        //         }
        //         added_constraints
        //     }
        //     (Ty::Func(r, s), Ty::Func(t, u)) if r.len() == t.len() => {
        //         self.add_constraint(
        //             EqConstraint::new(s.as_ref().clone(), u.as_ref().clone())
        //                 .with_info(info.clone()),
        //         );
        //         for (x, y) in r.iter().zip(t.iter()).rev() {
        //             self.add_constraint(
        //                 EqConstraint::new(x.clone(), y.clone()).with_info(info.clone()),
        //             )
        //         }
        //         true
        //     }
        //     (Ty::Qualified(p, s), Ty::Qualified(q, t)) if p == q => {
        //         self.add_constraint(
        //             EqConstraint::new(s.as_ref().clone(), t.as_ref().clone())
        //                 .with_info(info.clone()),
        //         );
        //         true
        //     }
        //     (Ty::Qualified(_, s), t) => self.unify_terms(s, t, info),
        //     (s, Ty::Qualified(_, t)) => self.unify_terms(s, t, info),
        //     (Ty::All(xs, s), Ty::All(ys, t)) if xs.len() == ys.len() => {
        //         self.add_constraint(
        //             EqConstraint::new(s.as_ref().clone(), t.as_ref().clone())
        //                 .with_info(info.clone()),
        //         );
        //         true
        //     }
        //     (Ty::All(_, s), t) => self.unify_terms(s, t, info),
        //     (s, Ty::All(_, t)) => self.unify_terms(s, t, info),
        //     _ => false, // return Err(InferError {
        //                 //     msg: format!("type mismatch `{}` and `{}`", a, b),
        //                 //     src: vec![],
        //                 // })
        // }
    }

    fn make_consistent(&mut self) {
        // do nothing
    }

    fn subst_var(&mut self, v: TyVar, ty: Ty) {
        self.subst.insert(v, ty);
    }
}

impl<'a> HasState for GreedySolver<'a> {
    fn new_tvar(&mut self) -> TyVar {
        self.ctx.new_tvar()
    }

    fn new_svar(&mut self) -> TyVar {
        self.ctx.new_svar()
    }

    fn get_tf(&mut self) -> RefMut<TyVarFactory> {
        self.ctx.tf_mut()
    }

    fn get_sf(&mut self) -> RefMut<TyVarFactory> {
        self.ctx.sf_mut()
    }

    fn store_ty(&mut self, v: TyVar, ty: Ty, info: ConstraintInfo) {
        self.ty_map.insert(v, (ty, info));
    }

    fn lookup_ty(&self, tv: &TyVar) -> Option<Ty> {
        self.ty_map.get(tv).cloned().map(|(t, _)| t)
    }

    fn find_ty(&self, r: &Ty) -> Ty {
        match r {
            Ty::Var(tv) => self.lookup_ty(tv).unwrap_or_else(|| r.clone()),
            _ => r.clone(),
        }
    }

    fn add_skolems(&mut self, info: &ConstraintInfo, skolems: Vec<TyVar>, monos: Vec<TyVar>) {
        self.skolems.push((skolems, monos, info.clone()));
    }
}

impl<'a> HasPredicates for GreedySolver<'a> {
    fn get_preds(&self) -> &Vec<(TyPredicate, ConstraintInfo)> {
        &self.prove_preds
    }

    fn assume_pred(&mut self, p: TyPredicate, info: ConstraintInfo) {
        self.assume_preds.push((p, info));
    }

    fn prove_pred(&mut self, p: TyPredicate, info: ConstraintInfo) {
        self.prove_preds.push((p, info));
    }

    fn generalize_with_preds(&mut self, mono_tys: &Vec<Ty>, ty: Ty) -> Ty {
        // get all of the predicates
        let p = self.prove_preds.drain(..).collect::<Vec<_>>();
        let q = self.generalized_preds.drain(..).collect::<Vec<_>>();

        // collect the free variables
        let vs = ty
            .free_vars()
            .difference(&mono_tys.free_vars())
            .map(|&v| v)
            .collect::<HashSet<_>>();

        // split the prove predicates into a set that do not
        // contain the free variables and another that does
        let (a, b) = p
            .into_iter()
            .partition::<Vec<_>, _>(|(p, _)| !p.free_vars().is_disjoint(&vs));

        // same but for the generalized predicates
        let c = q
            .into_iter()
            .filter(|(p, _)| !p.free_vars().is_disjoint(&vs))
            .collect::<Vec<_>>();

        // re-add the ones that were split off
        self.prove_preds.extend(b);
        self.generalized_preds.extend(a.clone());

        // collect all of the predicates and generalize the type
        let preds = a.into_iter().chain(c.into_iter()).map(|(p, _)| p).collect();
        ty.generalize(&mono_tys, &preds)
    }
}

#[cfg(test)]
mod greedy_solver_tests {
    use crate::typing::{
        top::{
            constraints::{EqConstraint, ImplicitConstraint},
            solvers::Solver,
        },
        ty::Ty,
        Ctx, InferError,
    };

    use super::GreedySolver;

    #[test]
    fn test_greedy_solver() -> Result<(), InferError> {
        let constraints = vec![
            // v2 ≡ v1 → v0
            EqConstraint::new(
                Ty::Var(tvar!(v2)),
                Ty::Func(vec![Ty::Var(tvar!(v1))], Box::new(Ty::Var(tvar!(v0)))),
            ),
            // v1 ≡ v0
            EqConstraint::new(Ty::Var(tvar!(v1)), Ty::Var(tvar!(v0))),
            // v3 ≡ v4 → v5
            EqConstraint::new(
                Ty::Var(tvar!(v3)),
                Ty::Func(vec![Ty::Var(tvar!(v4))], Box::new(Ty::Var(tvar!(v5)))),
            ),
            // v3 ≤∅ v2
            ImplicitConstraint::new(vec![], Ty::Var(tvar!(v3)), Ty::Var(tvar!(v2))),
            // v4 ≤∅ v2
            ImplicitConstraint::new(vec![], Ty::Var(tvar!(v4)), Ty::Var(tvar!(v2))),
            // v6 ≡ v5
            EqConstraint::new(Ty::Var(tvar!(v6)), Ty::Var(tvar!(v5))),
        ];

        let mut ctx = Ctx::new();
        ctx.tf_mut().skip_to(7);
        let solver = GreedySolver::new(constraints, &mut ctx);
        let (sol, _) = solver.solve();

        assert_eq!(
            sol.subst,
            subst! {
                tvar!(v1) => Ty::Var(tvar!(v0)),
                tvar!(v2) => Ty::Func(vec![Ty::Var(tvar!(v0))], Box::new(Ty::Var(tvar!(v0)))),
                tvar!(v3) => Ty::Func(vec![Ty::Func(vec![Ty::Var(tvar!(v8))], Box::new(Ty::Var(tvar!(v8)))),], Box::new(Ty::Func(vec![Ty::Var(tvar!(v8))], Box::new(Ty::Var(tvar!(v8)))))),
                tvar!(v4) => Ty::Func(vec![Ty::Var(tvar!(v8))], Box::new(Ty::Var(tvar!(v8)))),
                tvar!(v5) => Ty::Func(vec![Ty::Var(tvar!(v8))], Box::new(Ty::Var(tvar!(v8)))),
                tvar!(v6) => Ty::Func(vec![Ty::Var(tvar!(v8))], Box::new(Ty::Var(tvar!(v8)))),
                tvar!(v7) => Ty::Func(vec![Ty::Var(tvar!(v8))], Box::new(Ty::Var(tvar!(v8))))
            }
        );

        Ok(())
    }
}

use std::{
    cell::RefMut,
    collections::{HashMap, HashSet, VecDeque},
};

use crate::typing::{
    constraints::{Constraint, ConstraintInfo, EqConstraint},
    predicate::TyPredicate,
    state::TyVarFactory,
    traits::{Generalize, HasBasic, HasFreeVars, HasPredicates, HasState, HasSubst},
    ty::{Ty, TyVar},
    ApplySubst, Ctx, Subst,
};

use super::{Solution, Solver};

#[derive(Debug)]
pub struct GreedySolver<'a> {
    ctx: &'a mut Ctx,
    subst: Subst,
    skolems: Vec<(Vec<TyVar>, Vec<TyVar>, ConstraintInfo)>,
    original_preds: Vec<TyPredicate>,
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
            original_preds: vec![],
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
            original_preds,
            assume_preds,
            prove_preds,
            generalized_preds,
            ty_map,
            ..
        } = self;

        // collect the type map of generalized types
        let ty_map = ty_map.into_iter().map(|(v, (t, _))| (v, t)).collect();

        // collect and dedup all of the predicates
        let mut preds = original_preds;
        preds.extend(
            prove_preds
                .into_iter()
                .chain(assume_preds.into_iter())
                .chain(generalized_preds.into_iter())
                .map(|(p, _)| p),
        );

        preds.sort();
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

        self.original_preds
            .extend(prove_preds.iter().map(|(p, _)| p.clone()));
        self.original_preds
            .extend(assume_preds.iter().map(|(p, _)| p.clone()));
        self.original_preds
            .extend(generalized_preds.iter().map(|(p, _)| p.clone()));
        self.original_preds.sort();
        self.original_preds.dedup();

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
    }

    fn make_consistent(&mut self) {
        // do nothing
    }

    fn subst_var(&mut self, v: TyVar, ty: Ty) {
        self.subst.insert(v, ty);
    }

    fn get_var(&self, v: &Ty) -> Ty {
        v.clone().apply_subst(&self.subst)
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
        constraints::{EqConstraint, ImplicitConstraint},
        solvers::Solver,
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

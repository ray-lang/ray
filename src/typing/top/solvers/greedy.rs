use std::collections::{HashMap, VecDeque};

use crate::typing::{
    top::state::TyVarFactory,
    ty::{Ty, TyVar},
    ApplySubst, ApplySubstMut, Subst,
};

use crate::typing::top::{
    constraints::{Constraint, ConstraintInfo},
    traits::{HasBasic, HasState, HasSubst},
};

use super::Solver;

#[derive(Debug)]
pub struct GreedySolver<'a> {
    tvar_factory: &'a mut TyVarFactory,
    svar_factory: &'a mut TyVarFactory,
    subst: Subst,
    constraints: VecDeque<Constraint>,
    tys: HashMap<TyVar, (Ty, ConstraintInfo)>,
}

impl<'a> GreedySolver<'a> {
    pub fn new(
        tvar_factory: &'a mut TyVarFactory,
        svar_factory: &'a mut TyVarFactory,
        constraints: Vec<Constraint>,
    ) -> GreedySolver<'a> {
        GreedySolver {
            tvar_factory,
            svar_factory,
            constraints: constraints.into(),
            subst: Subst::new(),
            tys: HashMap::new(),
        }
    }
}

impl<'a> Solver for GreedySolver<'a> {}

impl<'a> HasBasic for GreedySolver<'a> {
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

    fn add_error(&mut self, info: ConstraintInfo) {
        todo!()
    }

    fn get_errors(&self) -> Vec<ConstraintInfo> {
        todo!()
    }

    fn add_check<F>(&mut self, msg: String, check: F)
    where
        F: Fn() -> bool,
    {
        todo!()
    }
}

impl<'a> HasSubst for GreedySolver<'a> {
    fn apply_subst(&mut self) {
        let constraints = std::mem::take(&mut self.constraints);
        self.constraints = constraints.apply_subst(&self.subst);
    }

    fn get_subst(&self) -> &Subst {
        &self.subst
    }

    fn unify_terms(&mut self, a: &Ty, b: &Ty) -> Result<(), String> {
        let sub = a.mgu(b)?;
        println!("subst: {}", sub);
        self.subst.apply_subst_mut(&sub);
        println!("apply subst to subst: {}", self.subst);
        println!("union: {} U {}", self.subst, sub);
        self.subst
            .try_union_inplace(sub, |ty, other_ty| ty.mgu(other_ty))?;
        println!("union result: {}", self.subst);
        Ok(())
    }

    fn make_consistent(&mut self) {
        // do nothing
    }

    fn subst_var(&mut self, v: TyVar, ty: Ty) {
        self.subst.insert(v, ty);
    }
}

impl<'a> HasState for GreedySolver<'a> {
    fn next_tvar(&mut self) -> TyVar {
        self.tvar_factory.next()
    }

    fn next_svar(&mut self) -> TyVar {
        self.svar_factory.next()
    }

    fn store_ty(&mut self, v: TyVar, ty: Ty, info: ConstraintInfo) {
        self.tys.insert(v, (ty, info));
    }

    fn lookup_ty(&self, v: &TyVar) -> Ty {
        todo!()
    }

    fn find_ty(&self, r: &Ty) -> Ty {
        match r {
            Ty::Var(tv) => self
                .tys
                .get(tv)
                .cloned()
                .map(|(t, _)| t)
                .unwrap_or_else(|| r.clone()),
            _ => r.clone(),
        }
    }

    fn add_skolems(&mut self, info: &ConstraintInfo, skolems: Vec<TyVar>, tyvars: Vec<TyVar>) {
        todo!(
            "add_skolems: [{}]",
            skolems
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    fn instantiate(&mut self, ty: Ty, reverse_subst: &mut HashMap<TyVar, TyVar>) -> Ty {
        match ty {
            Ty::Var(v) => {
                if let Some(v) = reverse_subst.get(&v) {
                    Ty::Var(v.clone())
                } else {
                    let u = self.next_tvar();
                    reverse_subst.insert(v, u.clone());
                    Ty::Var(u)
                }
            }
            Ty::Literal(k, v) => {
                if let Some(v) = reverse_subst.get(&v) {
                    Ty::Literal(k, v.clone())
                } else {
                    let u = self.next_tvar();
                    reverse_subst.insert(v, u.clone());
                    Ty::Literal(k, u)
                }
            }
            Ty::Union(tys) => Ty::Union(
                tys.into_iter()
                    .map(|t| self.instantiate(t, reverse_subst))
                    .collect(),
            ),
            Ty::Func(p, r) => Ty::Func(
                p.into_iter()
                    .map(|t| self.instantiate(t, reverse_subst))
                    .collect(),
                Box::new(self.instantiate(*r, reverse_subst)),
            ),
            Ty::Projection(s, tys) => Ty::Projection(
                s,
                tys.into_iter()
                    .map(|t| self.instantiate(t, reverse_subst))
                    .collect(),
            ),
            Ty::Constrained(_, t) | Ty::All(_, t) => self.instantiate(*t, reverse_subst),
            t => t,
        }
    }
}

#[cfg(test)]
mod greedy_solver_tests {
    use crate::typing::{
        top::{
            constraints::{Constraint, EqConstraint, ImplicitConstraint},
            solvers::Solver,
            state::TyVarFactory,
        },
        ty::{Ty, TyVar},
    };

    use super::GreedySolver;

    #[test]
    fn test_greedy_solver() -> Result<(), String> {
        let constraints = vec![
            // v2 ≡ v1 → v0
            Constraint::new(EqConstraint(
                Ty::Var(tvar!(v2)),
                Ty::Func(vec![Ty::Var(tvar!(v1))], Box::new(Ty::Var(tvar!(v0)))),
            )),
            // v1 ≡ v0
            Constraint::new(EqConstraint(Ty::Var(tvar!(v1)), Ty::Var(tvar!(v0)))),
            // v3 ≡ v4 → v5
            Constraint::new(EqConstraint(
                Ty::Var(tvar!(v3)),
                Ty::Func(vec![Ty::Var(tvar!(v4))], Box::new(Ty::Var(tvar!(v5)))),
            )),
            // v3 ≤∅ v2
            Constraint::new(ImplicitConstraint(
                vec![],
                Ty::Var(tvar!(v3)),
                Ty::Var(tvar!(v2)),
            )),
            // v4 ≤∅ v2
            Constraint::new(ImplicitConstraint(
                vec![],
                Ty::Var(tvar!(v4)),
                Ty::Var(tvar!(v2)),
            )),
            // v6 ≡ v5
            Constraint::new(EqConstraint(Ty::Var(tvar!(v6)), Ty::Var(tvar!(v5)))),
        ];

        let mut tf = TyVarFactory::new("v");
        tf.skip_to(7);

        let mut sf = TyVarFactory::new("s");
        let mut solver = GreedySolver::new(&mut tf, &mut sf, constraints);
        solver.start_solving()?;

        assert_eq!(
            solver.subst,
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

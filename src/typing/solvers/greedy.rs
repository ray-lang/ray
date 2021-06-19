use std::collections::HashMap;

use crate::{
    convert::ToSet,
    typing::{
        constraints::{Constraint, ConstraintInfo, ConstraintList, EqConstraint},
        predicate::TyPredicate,
        state::TyVarFactory,
        traits::{
            CollectTyVars, Generalize, HasBasic, HasFreeVars, HasPredicates, HasState, HasSubst,
            QualifyTypes, QuantifyTypes,
        },
        ty::{Ty, TyVar},
        ApplySubst, Subst, TyCtx,
    },
};

use super::{Solution, Solver};

#[derive(Debug)]
pub struct GreedySolver<'a> {
    ctx: &'a mut TyCtx,
    subst: Subst,
    skolems: Vec<(Vec<TyVar>, Vec<TyVar>, ConstraintInfo)>,
    original_preds: Vec<TyPredicate>,
    assume_preds: Vec<(TyPredicate, ConstraintInfo)>,
    prove_preds: Vec<(TyPredicate, ConstraintInfo)>,
    generalized_preds: Vec<(TyPredicate, ConstraintInfo)>,
    constraints: ConstraintList,
    ty_map: HashMap<TyVar, (Ty, ConstraintInfo)>,
    inst_map: Subst,
    skol_map: Subst,
}

impl<'a> GreedySolver<'a> {
    pub fn new<T: Into<ConstraintList>>(constraints: T, ctx: &'a mut TyCtx) -> GreedySolver<'a> {
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
            inst_map: Subst::new(),
            skol_map: Subst::new(),
        }
    }
}

impl<'a> Solver for GreedySolver<'a> {
    fn solution(self) -> Solution {
        let GreedySolver {
            mut subst,
            original_preds,
            assume_preds,
            prove_preds,
            generalized_preds,
            ty_map,
            inst_map,
            skol_map,
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

        // qualify all types in the substitution
        subst.qualify_tys(&preds);

        // quantify all types in the substitution
        subst.quantify_tys();

        Solution {
            subst,
            ty_map,
            inst_map,
            skol_map,
            preds,
        }
    }
}

impl<'a> HasBasic for GreedySolver<'a> {
    fn ctx(&self) -> &TyCtx {
        &self.ctx
    }

    fn get_constraints_mut(&mut self) -> &mut ConstraintList {
        &mut self.constraints
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
                new_sub.union_on_conflict(sub, |new_ty, existing_ty| {
                    // if new_ty.is_nullary() && existing_ty.is_nullary() {
                    //     log::debug!("new_ty = {}; existing_ty = {}", new_ty, existing_ty);
                    //     let mut ty = existing_ty.clone();
                    //     ty.union(new_ty.clone());
                    //     log::debug!("union ty = {}", ty);
                    //     Some(ty)
                    // } else {
                    self.unify_terms(new_ty, existing_ty, info);
                    None
                    // }
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
    fn tf(&mut self) -> &mut TyVarFactory {
        self.ctx.tf()
    }

    fn sf(&mut self) -> &mut TyVarFactory {
        self.ctx.sf()
    }

    fn store_ty(&mut self, v: TyVar, ty: Ty, info: ConstraintInfo) {
        self.ty_map.insert(v, (ty, info));
    }

    fn lookup_ty(&self, tv: &TyVar) -> Option<Ty> {
        self.ty_map.get(tv).cloned().map(|(t, _)| t)
    }

    fn inst_ty(&mut self, v: Ty, u: Ty) {
        // type `v` is an instance of `u`
        if let Ty::Var(v) = v {
            self.inst_map.insert(v, u);
        }
    }

    fn skol_ty(&mut self, v: Ty, u: Ty) {
        // type `v` is a skolemized type of `u`
        if let Ty::Var(v) = v {
            self.skol_map.insert(v, u);
        }
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
    fn get_preds(&self) -> Vec<&(TyPredicate, ConstraintInfo)> {
        self.prove_preds
            .iter()
            .chain(self.generalized_preds.iter())
            .collect()
    }

    fn assume_pred(&mut self, p: TyPredicate, info: ConstraintInfo) {
        self.assume_preds.push((p, info));
    }

    fn prove_pred(&mut self, p: TyPredicate, info: ConstraintInfo) {
        self.prove_preds.push((p, info));
    }

    fn generalize_with_preds(&mut self, mono_tys: &Vec<Ty>, ty: Ty) -> Ty {
        // collect the free variables
        let mono_tvs = mono_tys.collect_tyvars();
        let vs = ty
            .free_vars()
            .difference(&mono_tvs.iter().to_set())
            .map(|&v| v)
            .to_set();

        // move the prove predicates into a set that contains the freevars
        let mut i = 0;
        let mut prove_preds = vec![];
        while i < self.prove_preds.len() {
            let (p, _) = &self.prove_preds[i];
            if !p.free_vars().is_disjoint(&vs) {
                prove_preds.push(self.prove_preds.remove(i));
            } else {
                i += 1;
            }
        }

        // same but for the generalized predicates
        let gen_preds = self
            .generalized_preds
            .iter()
            .filter(|(p, _)| !p.free_vars().is_disjoint(&vs))
            .cloned()
            .collect::<Vec<_>>();

        // add the preds from prove preds that are to be used in the generalization
        self.generalized_preds.extend(prove_preds.clone());

        // collect all of the predicates and generalize the type
        let preds = prove_preds
            .into_iter()
            .chain(gen_preds.into_iter())
            .map(|(p, _)| p)
            .collect();
        ty.generalize(&mono_tys, &preds)
    }
}

#[cfg(test)]
mod greedy_solver_tests {
    use std::io;

    use crate::{
        ast::Path,
        typing::{
            constraints::{EqConstraint, ImplicitConstraint, SkolConstraint, VarConstraint},
            predicate::TyPredicate,
            solvers::Solver,
            ty::{TraitTy, Ty},
            InferError, TyCtx,
        },
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

        let mut ctx = TyCtx::new();
        ctx.tf().skip_to(7);
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

    #[test]
    fn test_annotated_types() -> Result<(), InferError> {
        fern::Dispatch::new()
            .level(log::LevelFilter::Debug)
            .chain(io::stderr())
            .apply()
            .unwrap();

        let constraints = vec![
            // v0 ≡ (v1) -> ()
            EqConstraint::new(
                Ty::Var(tvar!(v0)),
                Ty::Func(vec![Ty::Var(tvar!(v1))], Box::new(Ty::unit())),
            ),
            // v0 ≽ (string) -> ()
            SkolConstraint::new(
                vec![],
                Ty::Var(tvar!(v0)),
                Ty::Func(vec![Ty::string()], Box::new(Ty::unit())),
            ),
            // v2 ≡ (v3) -> ()
            EqConstraint::new(
                Ty::Var(tvar!(v2)),
                Ty::Func(vec![Ty::Var(tvar!(v3))], Box::new(Ty::unit())),
            ),
            // v2 ≽ All['a]('a) -> () where ToStr['a]
            SkolConstraint::new(
                vec![],
                Ty::Var(tvar!(v2)),
                Ty::All(
                    vec![tvar!('a)],
                    Box::new(Ty::Qualified(
                        vec![TyPredicate::Trait(Ty::Projection(
                            str!("ToStr"),
                            vec![Ty::Var(tvar!('a))],
                        ))],
                        Box::new(Ty::Func(vec![Ty::Var(tvar!('a))], Box::new(Ty::unit()))),
                    )),
                ),
            ),
        ];

        let mut ctx = TyCtx::new();
        ctx.add_trait_ty(
            str!("ToStr"),
            TraitTy {
                path: Path::from("ToStr"),
                ty: Ty::Projection(str!("ToStr"), vec![Ty::Var(tvar!('a))]),
                super_traits: vec![],
                fields: vec![(
                    str!("to_str"),
                    Ty::All(
                        vec![tvar!('a)],
                        Box::new(Ty::Func(vec![Ty::Var(tvar!('a))], Box::new(Ty::unit()))),
                    ),
                )],
            },
        );
        ctx.tf().skip_to(4);
        let solver = GreedySolver::new(constraints, &mut ctx);
        let (sol, _) = solver.solve();
        println!("{:#?}", sol);

        Ok(())
    }

    #[test]
    fn test_union_type() -> Result<(), InferError> {
        fern::Dispatch::new()
            .level(log::LevelFilter::Debug)
            .chain(io::stderr())
            .apply()
            .unwrap();

        let constraints = vec![
            // v0 ≡ string
            VarConstraint::new(tvar!(v0), Ty::string()),
            // v1 ≡ nil
            VarConstraint::new(tvar!(v1), Ty::nil()),
            // v2 ≡ v0
            VarConstraint::new(tvar!(v2), Ty::Var(tvar!(v0))),
            // v2 ≡ v1
            VarConstraint::new(tvar!(v2), Ty::Var(tvar!(v1))),
        ];

        let mut ctx = TyCtx::new();
        ctx.tf().skip_to(3);
        let solver = GreedySolver::new(constraints, &mut ctx);
        let (sol, _) = solver.solve();
        println!("{:#?}", sol);

        Ok(())
    }
}

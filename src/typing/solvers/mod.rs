mod greedy;

pub use greedy::*;

use crate::typing::{
    predicate::TyPredicate,
    ty::{Ty, TyVar},
    ApplySubst, InferError, Subst, TyCtx,
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
    pub unformalized_inst_map: Subst,
    pub skol_map: Subst,
    pub skolem_subst: Subst,
    pub preds: Vec<TyPredicate>,
}

impl std::fmt::Debug for Solution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Solution")
            .field("subst", &self.subst)
            .field("ty_map", &self.ty_map)
            .field("inst_map", &self.inst_map)
            .field("unformalized_inst_map", &self.unformalized_inst_map)
            .field("skol_map", &self.skol_map)
            .field("skolem_subst", &self.skolem_subst)
            .field("preds", &self.preds)
            .finish()
    }
}

impl ApplySubst for Solution {
    fn apply_subst(mut self, subst: &Subst) -> Self {
        self.subst = self.subst.apply_subst(&subst);
        self.ty_map = self.ty_map.apply_subst(&self.subst);
        self.inst_map = self.inst_map.apply_subst(&self.subst);
        self.skol_map = self.skol_map.apply_subst(&self.subst);
        self.preds = self.preds.apply_subst(&self.subst);
        self.preds.sort();
        self.preds.dedup();
        self
    }
}

impl Solution {
    pub fn satisfies(&self, constraints: Vec<Constraint>, ctx: &TyCtx) -> Vec<InferError> {
        let mut errs = vec![];
        for c in constraints.into_iter().rev() {
            if let Some(e) = self.satisfies_constraint(c, ctx).err() {
                errs.push(e);
            }
        }

        errs
    }

    fn satisfies_constraint(&self, c: Constraint, ctx: &TyCtx) -> Result<(), InferError> {
        c.satisfied_by(self, ctx)
    }

    pub fn apply_subst_changes(&mut self) {
        let subst = self.subst.clone();
        self.apply_subst_mut(&subst);
        self.ty_map.qualify_tys(&self.preds);
    }

    pub fn formalize_types(&mut self) {
        // formalize any unbound type variables
        let mut subst = Subst::new();
        for ty in self.ty_map.values() {
            let ty: Ty = ty.clone().apply_subst(&self.subst);
            if ty.is_func() {
                subst.extend(ty.formalize());
            } else if let Ty::All(_, t) = ty {
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
            }
        }

        // add to substitution from the original skolem variables
        for (sk, ty) in self.skolem_subst.iter() {
            // get the current type variable from the substitution
            let tv = sk.clone().apply_subst(&self.subst);
            // add this to the substitution
            subst.insert(tv, ty.clone());
        }

        // let subst = self.subst.clone();
        log::debug!("apply subst: {:#?}", subst);
        self.subst.extend(subst);
        self.apply_subst_changes();

        self.unformalized_inst_map.extend(self.inst_map.clone());

        // for (var, ty) in self.skol_map.iter() {
        //     match self.subst.get(var).cloned() {
        //         Some(other_ty) if other_ty.has_unknowns() => {
        //             log::debug!("ty: {}", ty);
        //             log::debug!("other_ty: {}", other_ty);
        //             let ty = ty.clone().apply_subst(&self.subst);
        //             let other_ty = other_ty.apply_subst(&self.subst);
        //             let sub = other_ty.mgu(&ty).unwrap_or_default();
        //             log::debug!("sub: {}", sub);
        //             self.subst.union_inplace(sub);
        //         }
        //         _ => continue,
        //     }
        // }

        // let subst = self.subst.clone();
        // self.apply_subst_mut(&subst);

        // for (var, ty) in self.inst_map.iter() {
        //     match self.subst.get(var).cloned() {
        //         Some(other_ty) if other_ty.has_unknowns() => {
        //             let ty = ty.clone().apply_subst(&self.subst);
        //             let other_ty = other_ty.apply_subst(&self.subst);
        //             log::debug!("ty: {}", ty);
        //             log::debug!("other_ty: {}", other_ty);
        //             let sub = other_ty.mgu(&ty).unwrap_or_default();
        //             log::debug!("sub: {}", sub);
        //             self.subst.union_inplace(sub);
        //         }
        //         _ => continue,
        //     }
        // }

        // let subst = self.subst.clone();
        // self.apply_subst_mut(&subst);
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

    pub fn get_var(&self, v: &TyVar) -> Result<Ty, InferError> {
        if let Some(s) = self.subst.get(v) {
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
            match pred {
                TyPredicate::Trait(t) => match t {
                    Ty::Projection(x, p) => {
                        if x == "core::Int" || x == "core::Float" {
                            let base_ty = &p[0];
                            if base_ty.is_tyvar() {
                                cs.push(
                                    EqConstraint::new(
                                        base_ty.clone(),
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
                },
                _ => continue,
            }
        }

        self.add_constraints(cs);
        self.solve_constraints(&mut check);

        let mut cs = vec![];
        for (pred, info) in self.get_preds() {
            match pred {
                TyPredicate::HasMember(ty, member_name, member_ty) => {
                    let fqn = match ty.get_path() {
                        Some(p) => p,
                        _ => continue,
                    };
                    let st = match self.ctx().get_struct_ty(&fqn) {
                        Some(st) => st,
                        _ => continue,
                    };
                    if let Some((_, f)) = st.get_field(member_name) {
                        cs.push(
                            EqConstraint::new(member_ty.clone(), f.clone()).with_info(info.clone()),
                        );
                    }
                }
                _ => continue,
            }
        }

        self.add_constraints(cs);
        self.solve_constraints(&mut check);

        let mut solution = self.solution();
        log::debug!("------------- Before constraint apply_subst ---------------");
        log::debug!("solution: {:#?}", solution);
        let mut check = check.apply_subst(&solution.subst);
        // check.qualify_tys(&solution.preds);
        // check.quantify_tys();

        log::debug!("------------- Before formalization ---------------");
        log::debug!("constraints to check: {:#?}", check);
        log::debug!("solution: {:#?}", solution);

        solution.formalize_types();

        check = check.apply_subst(&solution.subst);
        check.qualify_tys(&solution.preds);
        check.quantify_tys();

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
            ConstraintKind::Var(c) => {
                let (v, t) = c.unpack();
                if self.unify_terms(&Ty::Var(v), &t, &info) {
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
                let t_sub = s.instantiate(&mut self.tf());
                let (p, t_sub) = t_sub.unpack_qualified_ty();
                for pred in p {
                    self.add_constraint(ProveConstraint::new(pred).with_info(info.clone()))
                }

                self.add_constraint(EqConstraint::new(t, t_sub).with_info(info));
            }
            ConstraintKind::Skol(c) => {
                let (monos, t, r) = c.unpack();
                let s = self.find_ty(&r);
                self.skol_ty(t.clone(), s.clone());
                let (t_sub, skolems) = s.skolemize(&mut self.sf());
                log::debug!("t_sub = {}", t_sub);
                log::debug!("s = {}", s);
                let skolem_subst = t_sub.mgu(&s).unwrap();
                log::debug!("skolem_subst = {:#?}", skolem_subst);
                let info = info.skol_ty(&s);
                self.add_skolems(&info, skolems, monos, skolem_subst);

                let (p, t_sub) = t_sub.unpack_qualified_ty();
                for pred in p {
                    self.add_constraint(AssumeConstraint::new(pred).with_info(info.clone()))
                }
                self.add_constraint(EqConstraint::new(t, t_sub).with_info(info));
            }
            ConstraintKind::Implicit(c) => {
                let (tyvars, t1, t2) = c.unpack();
                let sv = self.sf().next();

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

// mod greedy;

// use std::{collections::HashSet, time::SystemTime};

// pub use greedy::*;

// use crate::typing::{
//     predicate::TyPredicate,
//     traits::CollectTyVars,
//     ty::{Ty, TyVar},
//     ApplySubst, Subst, TyCtx, TypeError,
// };

// use super::{
//     constraints::{
//         AssumeConstraint, Constraint, ConstraintKind, EqConstraint, GenConstraint, InstConstraint,
//         ProveConstraint, Satisfiable,
//     },
//     traits::{
//         HasBasic, HasPredicates, HasState, HasSubst, HoistTypes, Instantiate, PolymorphismInfo,
//         QualifyTypes, QuantifyTypes, Skolemize,
//     },
//     ApplySubstMut,
// };

// #[derive(Clone, PartialEq, Eq)]
// pub struct Solution {
//     pub subst: Subst,
//     pub ty_map: Subst,
//     pub inst_map: Subst,
//     pub unformalized_inst_map: Subst,
//     pub skol_map: Subst,
//     pub skolem_subst: Subst,
//     pub preds: Vec<TyPredicate>,
// }

// impl std::fmt::Debug for Solution {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         f.debug_struct("Solution")
//             .field("subst", &self.subst)
//             .field("ty_map", &self.ty_map)
//             .field("inst_map", &self.inst_map)
//             .field("unformalized_inst_map", &self.unformalized_inst_map)
//             .field("skol_map", &self.skol_map)
//             .field("skolem_subst", &self.skolem_subst)
//             .field("preds", &self.preds)
//             .finish()
//     }
// }

// impl ApplySubst for Solution {
//     fn apply_subst(mut self, subst: &Subst) -> Self {
//         self.subst = self.subst.apply_subst(&subst);
//         self.ty_map = self.ty_map.apply_subst(&self.subst);
//         self.inst_map = self.inst_map.apply_subst(&self.subst);
//         self.skol_map = self.skol_map.apply_subst(&self.subst);
//         self.preds = self.preds.apply_subst(&self.subst);
//         self.preds.sort();
//         self.preds.dedup();
//         self
//     }
// }

// impl Solution {
//     pub fn satisfies(&self, constraints: Vec<Constraint>, ctx: &TyCtx) -> Vec<TypeError> {
//         let mut errs = vec![];
//         for c in constraints.into_iter().rev() {
//             if let Some(e) = self.satisfies_constraint(c, ctx).err() {
//                 errs.push(e);
//             }
//         }

//         errs
//     }

//     fn satisfies_constraint(&self, c: Constraint, ctx: &TyCtx) -> Result<(), TypeError> {
//         c.satisfied_by(self, ctx)
//     }

//     pub fn apply_subst_changes(&mut self) {
//         let subst = self.subst.clone();
//         self.apply_subst_mut(&subst);
//     }

//     pub fn simplify_subst(&mut self) {
//         log::debug!("solution: {:#?}", self);

//         // first, qualify the types in the solution
//         self.subst.qualify_tys(&self.preds);
//         self.ty_map.qualify_tys(&self.preds);
//         self.inst_map.qualify_tys(&self.preds);

//         let tvs = self.subst.keys().cloned().collect::<Vec<_>>();
//         let mut tv_set = HashSet::new();
//         for tv in tvs {
//             self.simplify_var(tv, &mut tv_set);
//         }
//     }

//     fn simplify_var(&mut self, tv: TyVar, tv_set: &mut HashSet<TyVar>) {
//         log::debug!("simplify var: {:?} {:?}", tv, tv_set);
//         if tv_set.contains(&tv) {
//             return;
//         }

//         tv_set.insert(tv.clone());
//         let tyvars = unless!(self.subst.get(&tv).map(|ty| ty.collect_tyvars()));
//         for tv in tyvars {
//             self.simplify_var(tv, tv_set);
//         }

//         // unwrap is okay here because we wouldn't have gotten here if it was None
//         let ty = self.subst.get(&tv).cloned().unwrap();
//         let subst = Subst::one(tv, ty);
//         self.apply_subst_mut(&subst);
//         log::debug!("solution: {:#?}", self);
//     }

//     pub fn formalize_types(&mut self) {
//         log::debug!("solution: {:#?}", self);

//         let inst_map = self.inst_map.clone();
//         let prev_sub = self.subst.clone();
//         let mut inst_sub = Subst::new();
//         for (var, original_ty) in self.inst_map.iter() {
//             match prev_sub.get(var).cloned() {
//                 Some(inst_ty) if inst_ty.has_unknowns() => {
//                     // find all of the types that have been solved
//                     let solved_tyvars = inst_ty
//                         .collect_tyvars()
//                         .into_iter()
//                         .filter_map(|tv| {
//                             let mapped_ty = prev_sub.get_ty_for_var(&tv);
//                             log::debug!("tv: {}", tv);
//                             log::debug!("mapped_ty: {}", mapped_ty);

//                             // if the mapped type is not the original type var
//                             // and mapped type is either not a type variable or is
//                             // an unknown type variable, then the type is considered solved
//                             if !mapped_ty.is_unknown_tyvar() {
//                                 if let Ty::Var(u) = mapped_ty {
//                                     Some(u)
//                                 } else {
//                                     Some(tv)
//                                 }
//                             } else {
//                                 None
//                             }
//                         })
//                         .collect::<HashSet<_>>();

//                     let original_ty = original_ty.clone().apply_subst(&prev_sub);
//                     let mut inst_ty = inst_ty.apply_subst(&prev_sub);
//                     log::debug!("original_ty: {}", original_ty);
//                     log::debug!("inst_ty: {}", inst_ty);
//                     log::debug!("solved_tyvars: {:?}", solved_tyvars);
//                     // remove type vars from the substitution and
//                     // apply them to the instantiated type
//                     let mut sub = inst_ty.mgu(&original_ty).unwrap_or_default();
//                     let mut local_sub = Subst::new();
//                     for tv in solved_tyvars {
//                         if let Some(ty) = sub.remove(&tv) {
//                             local_sub.insert(tv, ty);
//                         }
//                     }
//                     log::debug!("sub: {}", sub);
//                     log::debug!("local_sub: {}", local_sub);
//                     for tv in sub.keys() {
//                         let mut ty = Ty::Var(tv.clone());
//                         ty.quantify_in_place();
//                         ty.qualify_in_place(&self.preds);
//                         inst_sub.insert(tv.clone(), ty);
//                     }

//                     self.subst.union_inplace(sub);

//                     inst_ty.quantify_in_place();
//                     inst_ty.apply_subst_mut(&local_sub);
//                     inst_ty.qualify_in_place(&self.preds);
//                     log::debug!("new instantiation: {} => {}", var, inst_ty);
//                     self.subst.insert(var.clone(), inst_ty);
//                 }
//                 _ => continue,
//             }
//         }

//         self.apply_subst_changes();
//         inst_sub.apply_subst_mut(&self.subst);
//         log::debug!("inst_sub: {:#?}", inst_sub);
//         log::debug!("solution: {:#?}", self);

//         // formalize any unbound type variables
//         let mut subst = Subst::new();
//         for ty in self.ty_map.values() {
//             let ty = ty.clone().apply_subst(&self.subst);
//             if ty.is_func() {
//                 todo!()
//                 // subst.extend(ty.formalize());
//             }
//         }

//         log::debug!("apply subst: {:#?}", subst);
//         self.subst.union_inplace(subst);
//         self.apply_subst_changes();
//         log::debug!("solution: {:#?}", self);

//         // use the inst_map from before
//         self.unformalized_inst_map.extend(inst_map);
//     }

//     pub fn get_ty(&self, r: Ty) -> Result<Ty, TypeError> {
//         Ok(if let Ty::Var(v) = r {
//             let r = self.ty_map.get(&v);
//             if r.is_none() {
//                 return Err(TypeError::tyvar(v));
//             }

//             r.unwrap().clone()
//         } else {
//             r
//         })
//     }

//     pub fn get_var(&self, v: &TyVar) -> Result<Ty, TypeError> {
//         if let Some(s) = self.subst.get(v) {
//             Ok(s.clone())
//         } else {
//             Err(TypeError::tyvar(v.clone()))
//         }
//     }
// }

// pub trait Solver: HasBasic + HasSubst + HasState + HasPredicates {
//     fn solution(self) -> Solution;

//     fn apply_subst_to<T>(&self, value: T) -> T
//     where
//         T: ApplySubst,
//     {
//         value.apply_subst(self.get_subst())
//     }

//     fn solve(mut self) -> (Solution, Vec<Constraint>)
//     where
//         Self: std::marker::Sized,
//     {
//         // first solve the constraints
//         let mut check = vec![];
//         self.solve_constraints(&mut check);

//         let mut cs = vec![];
//         for (pred, info) in self.get_preds() {
//             match pred {
//                 TyPredicate::HasMember(ty, member_name, member_ty) => {
//                     let fqn = match ty.get_path() {
//                         Some(p) => p,
//                         _ => continue,
//                     };
//                     let st = match self.ctx().get_struct_ty(&fqn) {
//                         Some(st) => st,
//                         _ => continue,
//                     };
//                     if let Some((_, f)) = st.get_field(member_name) {
//                         cs.push(EqConstraint::new(member_ty, f).with_info(info.clone()));
//                     }
//                 }
//                 _ => continue,
//             }
//         }

//         self.add_constraints(cs);
//         self.solve_constraints(&mut check);

//         let mut solution = self.solution();
//         log::debug!("------------- Before constraint apply_subst ---------------");
//         log::debug!("solution: {:#?}", solution);
//         check.apply_subst_mut(&solution.subst);
//         check.qualify_tys(&solution.preds);
//         check.quantify_tys();

//         log::debug!("------------- Before subst simplification ---------------");
//         log::debug!("constraints to check: {:#?}", check);
//         log::debug!("solution: {:#?}", solution);

//         solution.simplify_subst();
//         check.apply_subst_mut(&solution.subst);
//         check.qualify_tys(&solution.preds);
//         check.quantify_tys();

//         log::debug!("------------- Before formalization ---------------");
//         log::debug!("constraints to check: {:#?}", check);
//         log::debug!("solution: {:#?}", solution);
//         // solution.formalize_types();
//         // check.apply_subst_mut(&solution.subst);

//         log::debug!("------------- After formalization ---------------");
//         log::debug!("constraints to check: {:#?}", check);
//         log::debug!("solution: {:#?}", solution);

//         (solution, check)
//     }

//     fn solve_constraints(&mut self, check: &mut Vec<Constraint>) {
//         while let Some(c) = self.pop_constraint() {
//             self.solve_constraint(c, check);
//             self.apply_subst();
//         }
//     }

//     fn solve_constraint(&mut self, c: Constraint, check: &mut Vec<Constraint>) {
//         log::debug!("solve {:?}", c);
//         let c_clone = c.clone();
//         let info = c.info;
//         match c.kind {
//             ConstraintKind::Eq(c) => {
//                 let (s, t) = c.unpack();
//                 if self.unify_terms(&s, &t, &info) {
//                     return;
//                 }
//             }
//             ConstraintKind::Var(c) => {
//                 let (v, t) = c.unpack();
//                 if self.unify_terms(&Ty::Var(v), &t, &info) {
//                     return;
//                 }
//             }
//             ConstraintKind::Gen(c) => {
//                 let (m, v, t) = c.unpack();
//                 self.make_consistent();
//                 let m = self.apply_subst_to(m);
//                 log::debug!("inst constraint: m = {:?}", m);
//                 let t = self.apply_subst_to(t);
//                 log::debug!("inst constraint: t = {}", t);
//                 let s = self.generalize_with_preds(&m, t);
//                 log::debug!("inst constraint: s = {}", s);
//                 self.store_ty(v, s, info);
//             }
//             ConstraintKind::Inst(c) => {
//                 log::debug!("inst constraint: {:?}", c);
//                 let (t, r) = c.unpack();
//                 let s = self.find_ty(&r);
//                 log::debug!("s = {}", s);
//                 self.inst_ty(t.clone(), s.clone());
//                 let info = info.inst_ty(&s);
//                 let t_sub = s.instantiate(&mut self.tf());
//                 log::debug!("t_sub = {}", t_sub);
//                 let (p, t_sub) = t_sub.unpack_qualified_ty();
//                 for pred in p {
//                     self.add_constraint(ProveConstraint::new(pred).with_info(info.clone()))
//                 }

//                 self.add_constraint(EqConstraint::new(t, t_sub).with_info(info));
//             }
//             ConstraintKind::Skol(c) => {
//                 let (monos, t, r) = c.unpack();
//                 let s = self.find_ty(&r);
//                 self.skol_ty(t.clone(), s.clone());
//                 let (t_sub, skolems) = s.skolemize(&mut self.sf());
//                 log::debug!("t_sub = {}", t_sub);
//                 log::debug!("s = {}", s);
//                 let skolem_subst = t_sub.mgu(&s).unwrap();
//                 log::debug!("skolem_subst = {:#?}", skolem_subst);
//                 let info = info.skol_ty(&s);
//                 self.add_skolems(&info, skolems, monos, skolem_subst);

//                 let (p, t_sub) = t_sub.unpack_qualified_ty();
//                 for pred in p {
//                     self.add_constraint(AssumeConstraint::new(pred).with_info(info.clone()))
//                 }
//                 self.add_constraint(EqConstraint::new(t, t_sub).with_info(info));
//             }
//             ConstraintKind::Implicit(c) => {
//                 let (tyvars, t1, t2) = c.unpack();
//                 let sv = self.sf().next();

//                 self.add_constraints(vec![
//                     InstConstraint::new(t1, Ty::Var(sv.clone())).with_info(info.clone()),
//                     GenConstraint::new(
//                         tyvars.into_iter().map(|tv| Ty::Var(tv.clone())).collect(),
//                         sv,
//                         t2,
//                     )
//                     .with_info(info),
//                 ]);
//             }
//             ConstraintKind::Prove(c) => self.prove_pred(c.get_predicate(), info),
//             ConstraintKind::Assume(c) => self.assume_pred(c.get_predicate(), info),
//         }

//         check.push(c_clone);
//     }
// }

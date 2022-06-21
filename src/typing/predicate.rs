// use std::collections::{HashMap, HashSet};

// use itertools::Dedup;
// use serde::{Deserialize, Serialize};

// use crate::{
//     ast::{self, Path},
//     errors::{RayError, RayErrorKind},
//     pathlib::FilePath,
//     span::{parsed::Parsed, Source},
// };

// use super::{
//     state::TyVarFactory,
//     // traits::{CollectTyVars, HasFreeVars, HoistTypes, Instantiate, Polymorphize},
//     ty::{LiteralKind, Ty, TyVar},
//     ApplySubst,
//     Subst,
//     TyCtx,
// };

// pub trait PredicateEntails<Other = Self> {
//     fn entails(&self, other: &Other, ctx: &TyCtx) -> bool;
// }

// #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
// pub enum TyPredicate {
//     Trait(Ty),
//     Literal(Ty, LiteralKind),
//     HasMember(Ty, String, Ty),
// }

// impl std::fmt::Debug for TyPredicate {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             TyPredicate::Trait(p) => write!(f, "{}", p),
//             TyPredicate::Literal(t, k) => write!(f, "{} is {}", t, k),
//             TyPredicate::HasMember(t, m, member_ty) => write!(f, "{} has {} : {}", t, m, member_ty),
//         }
//     }
// }

// impl std::fmt::Display for TyPredicate {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             TyPredicate::Trait(p) => write!(f, "{}", p),
//             TyPredicate::Literal(t, k) => write!(f, "{} is {}", t, k),
//             TyPredicate::HasMember(t, m, member_ty) => write!(f, "{} has {} : {}", t, m, member_ty),
//         }
//     }
// }

// impl ApplySubst for TyPredicate {
//     fn apply_subst(self, subst: &Subst) -> TyPredicate {
//         match self {
//             TyPredicate::Trait(p) => {
//                 // make sure that p is not an quantified or qualified type
//                 let (p, _, _) = p.apply_subst(subst).hoist_types();
//                 TyPredicate::Trait(p)
//             }
//             TyPredicate::Literal(t, k) => {
//                 let (t, _, _) = t.apply_subst(subst).hoist_types();
//                 TyPredicate::Literal(t, k)
//             }
//             TyPredicate::HasMember(t, m, member_ty) => {
//                 TyPredicate::HasMember(t.apply_subst(subst), m, member_ty.apply_subst(subst))
//             }
//         }
//     }
// }

// impl HasFreeVars for TyPredicate {
//     fn free_vars(&self) -> HashSet<&TyVar> {
//         match self {
//             TyPredicate::Trait(t) | TyPredicate::Literal(t, _) => t.free_vars(),
//             TyPredicate::HasMember(t, _, member_ty) => {
//                 let mut fv = t.free_vars();
//                 fv.extend(member_ty.free_vars());
//                 fv
//             }
//         }
//     }
// }

// impl CollectTyVars for TyPredicate {
//     fn collect_tyvars(&self) -> Vec<TyVar> {
//         match self {
//             TyPredicate::Trait(t) | TyPredicate::Literal(t, _) => t.collect_tyvars(),
//             TyPredicate::HasMember(t, _, member_ty) => {
//                 let mut tv = t.collect_tyvars();
//                 tv.extend(member_ty.collect_tyvars());
//                 tv
//             }
//         }
//     }
// }

// impl Polymorphize for TyPredicate {
//     fn polymorphize(self, tf: &mut TyVarFactory, subst: &mut HashMap<Ty, TyVar>) -> Self {
//         match self {
//             TyPredicate::Trait(t) => {
//                 let (name, mut params) = variant!(t, if Ty::Projection(a, b));
//                 let ty_arg = params.pop().unwrap().polymorphize(tf, subst);
//                 TyPredicate::Trait(Ty::Projection(name, vec![ty_arg]))
//             }
//             TyPredicate::Literal(t, k) => TyPredicate::Literal(t.polymorphize(tf, subst), k),
//             TyPredicate::HasMember(t, m, member_ty) => TyPredicate::HasMember(
//                 t.polymorphize(tf, subst),
//                 m,
//                 member_ty.polymorphize(tf, subst),
//             ),
//         }
//     }
// }

// impl Instantiate for TyPredicate {
//     fn instantiate(self, tf: &mut TyVarFactory) -> TyPredicate {
//         match self {
//             TyPredicate::Trait(p) => TyPredicate::Trait(p.instantiate(tf)),
//             TyPredicate::Literal(t, k) => TyPredicate::Literal(t.instantiate(tf), k),
//             TyPredicate::HasMember(t, m, member_ty) => {
//                 TyPredicate::HasMember(t.instantiate(tf), m, member_ty.instantiate(tf))
//             }
//         }
//     }
// }

// impl HoistTypes for TyPredicate {
//     fn hoist_types(self) -> (Self, Vec<TyVar>, Vec<TyPredicate>) {
//         match self {
//             TyPredicate::Trait(t) => {
//                 let (t, qs, ps) = t.hoist_types();
//                 (TyPredicate::Trait(t), qs, ps)
//             }
//             TyPredicate::Literal(t, k) => {
//                 let (t, qs, ps) = t.hoist_types();
//                 (TyPredicate::Literal(t, k), qs, ps)
//             }
//             TyPredicate::HasMember(t, n, m) => {
//                 let (ty, mut qs, mut ps) = t.hoist_types();
//                 let (m, mqs, mps) = m.hoist_types();
//                 qs.extend(mqs);
//                 qs.sort();
//                 qs.dedup();
//                 ps.extend(mps);
//                 ps.sort();
//                 ps.dedup();
//                 (TyPredicate::HasMember(ty, n, m), qs, ps)
//             }
//         }
//     }
// }

// impl PredicateEntails<Vec<TyPredicate>> for Vec<TyPredicate> {
//     fn entails(&self, q: &Vec<TyPredicate>, ctx: &TyCtx) -> bool {
//         log::debug!("{:?} entails {:?}", self, q);
//         q.iter().all(|q| self.entails(q, ctx))
//     }
// }

// impl PredicateEntails<TyPredicate> for Vec<TyPredicate> {
//     fn entails(&self, q: &TyPredicate, ctx: &TyCtx) -> bool {
//         log::debug!("{:?} entails {}", self, q);
//         match q {
//             TyPredicate::Trait(trait_ty) => {
//                 log::debug!("[entails] trait type: {}", trait_ty);
//                 let base_ty = trait_ty.get_ty_param_at(0);

//                 // look through all of the traits and find the traits that include
//                 // the trait type in `q` as a super trait, meaning find all of the
//                 // subtraits of the trait type
//                 let subtraits = ctx.get_subtraits(trait_ty);
//                 log::debug!("[entails] subtraits: {:?}", subtraits);
//                 if subtraits.into_iter().any(|s| {
//                     let s = s.clone();
//                     let tv = s.get_ty_param_at(0).clone().as_tyvar();
//                     let sub = subst! { tv => base_ty.clone() };
//                     let s = s.apply_subst(&sub);
//                     let p = TyPredicate::Trait(s);
//                     self.entails(&p, ctx)
//                 }) {
//                     return true;
//                 }

//                 // find all of the impls of the trait in `q`
//                 if let Some(impls) = ctx.get_impls(trait_ty) {
//                     impls
//                         .iter()
//                         .filter(|i| {
//                             // unify the base types
//                             let sub = i.base_ty.mgu(base_ty).unwrap_or_default();
//                             let lhs = i.base_ty.clone().apply_subst(&sub);
//                             let rhs = base_ty.clone().apply_subst(&sub);
//                             lhs == rhs
//                         })
//                         .all(|i| {
//                             // and then check that the predicates hold for the impl
//                             self.entails(&i.predicates, ctx)
//                         })
//                 } else {
//                     self.iter().any(|p| p == q)
//                 }
//             }
//             TyPredicate::Literal(t, k) => match k {
//                 LiteralKind::Int => t.is_int_ty(),
//                 LiteralKind::Float => t.is_float_ty(),
//             },
//             TyPredicate::HasMember(t, member, _) => {
//                 let fqn = unless!(t.get_path(), else return false);

//                 ctx.has_member(&fqn, member)
//                     || self.iter().any(|p| {
//                         match p {
//                             TyPredicate::Trait(trait_ty) => {
//                                 // find the trait predicates that include the type `t`
//                                 let ty_arg = trait_ty.get_ty_param_at(0);
//                                 if t == ty_arg {
//                                     let fqn = trait_ty.get_path().unwrap();
//                                     ctx.has_member(&fqn, member)
//                                 } else {
//                                     false
//                                 }
//                             }
//                             TyPredicate::HasMember(u, n, _) => t == u && member == n,
//                             _ => false,
//                         }
//                     })
//             }
//         }
//     }
// }

// impl TyPredicate {
//     pub fn from_ast_ty(
//         q: &Parsed<Ty>,
//         scope: &ast::Path,
//         filepath: &FilePath,
//         tcx: &mut TyCtx,
//     ) -> Result<TyPredicate, RayError> {
//         // resolve the type
//         let ty_span = *q.span().unwrap();
//         let mut q = q.clone_value();
//         q.resolve_ty(scope, tcx);

//         let (s, v) = match q {
//             Ty::Projection(s, v) => (s, v),
//             _ => {
//                 return Err(RayError {
//                     msg: str!("qualifier must be a trait type"),
//                     src: vec![Source {
//                         span: Some(ty_span),
//                         filepath: filepath.clone(),
//                         ..Default::default()
//                     }],
//                     kind: RayErrorKind::Type,
//                 })
//             }
//         };

//         if v.len() != 1 {
//             return Err(RayError {
//                 msg: format!("traits must have one type argument, but found {}", v.len()),
//                 src: vec![Source {
//                     span: Some(ty_span),
//                     filepath: filepath.clone(),
//                     ..Default::default()
//                 }],
//                 kind: RayErrorKind::Type,
//             });
//         }

//         let ty_arg = v[0].clone();
//         let fqn = Path::from(s.as_str());
//         log::debug!("converting from ast type: {}", fqn);
//         let trait_ty = match tcx.get_trait_ty(&fqn) {
//             Some(t) => t,
//             _ => {
//                 return Err(RayError {
//                     msg: format!("trait `{}` is not defined", fqn),
//                     src: vec![Source {
//                         span: Some(ty_span),
//                         filepath: filepath.clone(),
//                         ..Default::default()
//                     }],
//                     kind: RayErrorKind::Type,
//                 })
//             }
//         };

//         let trait_ty = trait_ty.ty.clone();
//         let ty_param = variant!(trait_ty.get_ty_param_at(0).clone(), if Ty::Var(t));
//         let sub = subst! { ty_param => ty_arg };
//         let trait_ty = trait_ty.apply_subst(&sub);
//         Ok(TyPredicate::Trait(trait_ty))
//     }

//     pub fn core_trait<T: Into<String>>(name: T) -> Self {
//         TyPredicate::Trait(Ty::Projection(
//             format!("core::{}", name.into()),
//             vec![Ty::var("'a")],
//         ))
//     }

//     pub fn is_int_trait(&self) -> bool {
//         matches!(self, TyPredicate::Trait(Ty::Projection(s, ..)) if s == "core::Int")
//     }

//     pub fn is_float_trait(&self) -> bool {
//         matches!(self, TyPredicate::Trait(Ty::Projection(s, ..)) if s == "core::Float")
//     }

//     pub fn in_hnf(&self) -> bool {
//         match self {
//             TyPredicate::Trait(t) => t.get_ty_param_at(0).in_hnf(),
//             TyPredicate::Literal(_, _) => todo!(),
//             TyPredicate::HasMember(t, _, _) => t.in_hnf(),
//         }
//     }

//     pub fn unpack(&self) -> Option<(&String, Option<&Vec<Ty>>)> {
//         match self {
//             TyPredicate::Trait(Ty::Projection(p, tps)) => Some((p, Some(tps))),
//             TyPredicate::Literal(_, _) | TyPredicate::HasMember(_, _, _) | _ => None,
//         }
//     }

//     pub fn type_params(&self) -> Option<&Vec<Ty>> {
//         match self {
//             TyPredicate::Trait(Ty::Projection(_, tps)) => Some(tps),
//             _ => None,
//         }
//     }

//     pub fn desc(&self) -> String {
//         match self {
//             TyPredicate::Trait(t) => format!("implement {}", t),
//             TyPredicate::Literal(_, k) => match k {
//                 LiteralKind::Int => str!("is an integer type"),
//                 LiteralKind::Float => str!("is a float type"),
//             },
//             TyPredicate::HasMember(_, m, _) => format!("has member `{}`", m),
//         }
//     }
// }

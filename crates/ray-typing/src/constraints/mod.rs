use crate::top::{EqualityConstraint, PolymorphismConstraint, Predicate, QualifierConstraint};

use std::collections::HashSet;

use itertools::Itertools;

use super::{
    assumptions::AssumptionSet,
    info::TypeSystemInfo,
    state::{Env, SigmaEnv, TyEnv},
    ty::{SigmaTy, Ty, TyVar},
};

pub mod tree;

pub type Constraint = crate::top::Constraint<TypeSystemInfo, Ty, TyVar>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct EqConstraint;

impl EqConstraint {
    pub fn new(lhs: Ty, rhs: Ty) -> Constraint {
        Constraint::Equality(EqualityConstraint::new(lhs, rhs, TypeSystemInfo::default()))
    }

    pub fn lift(aset: &AssumptionSet, env: &Env<Ty>) -> Vec<(String, Constraint)> {
        let mut cl = vec![];
        for (x, lhs_ty) in env.iter().sorted_by_key(|&(x, _)| x) {
            if let Some(tys) = aset.get(x) {
                for rhs_ty in tys.iter().sorted() {
                    cl.push((
                        rhs_ty.to_string(),
                        EqConstraint::new(lhs_ty.clone(), rhs_ty.clone()),
                    ));
                }
            } else {
                log::debug!("{} is not in the assumption set", x);
            }
        }

        cl
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct GenConstraint;

impl GenConstraint {
    pub fn new(mono_tys: Vec<Ty>, svar: TyVar, ty: Ty) -> Constraint {
        PolymorphismConstraint::generalize(
            svar,
            mono_tys.into_iter().map(|x| x.into()).collect(),
            ty.into(),
            TypeSystemInfo::default(),
        )
        .into()
    }
}

pub struct InstConstraint;

impl InstConstraint {
    pub fn new(ty: Ty, sigma: SigmaTy) -> Constraint {
        PolymorphismConstraint::instantiate(ty, sigma.take(), TypeSystemInfo::default()).into()
    }

    pub fn lift(aset: &AssumptionSet, sigs: &SigmaEnv) -> Vec<(String, Constraint)> {
        let mut cl = vec![];
        for (x, tys) in aset.iter().sorted_by_key(|&(x, _)| x) {
            let entry = sigs.get_key_value(x).or_else(|| {
                sigs.iter()
                    .find(|(sig_path, _)| sig_path.without_type_args() == *x)
            });

            if let Some((sig_path, rhs_ty)) = entry {
                log::debug!("sig: {} :: {}", sig_path, rhs_ty);
                if tys.is_empty() {
                    log::debug!("ty is EMPTY");
                }

                for lhs_ty in tys {
                    let inst = InstConstraint::new(lhs_ty.clone(), rhs_ty.clone());
                    log::debug!("creating instantiate constraint: {}", inst);
                    cl.push((lhs_ty.to_string(), inst));
                }
            } else {
                log::debug!("InstConstraint::lift: {} is not in the sigs", x);
            }
        }

        cl
    }
}

pub struct SkolConstraint;

impl SkolConstraint {
    pub fn new<I: IntoIterator<Item = TyVar>>(v: I, t: Ty, u: SigmaTy) -> Constraint {
        Constraint::Polymorphism(PolymorphismConstraint::skolemize(
            t,
            v.into_iter().map(|x| Ty::Var(x)).collect(),
            u.take(),
            TypeSystemInfo::default(),
        ))
    }

    pub fn lift(
        env: &TyEnv,
        sigs: &SigmaEnv,
        mono_tys: &HashSet<TyVar>,
    ) -> Vec<(String, Constraint)> {
        let mut cl = vec![];
        for (x, lhs_ty) in env.iter().sorted_by_key(|&(x, _)| x) {
            if let Some(rhs_ty) = sigs.get(x) {
                log::debug!("creating skolem constraint for {}: {:?}", x, rhs_ty);
                cl.push((
                    lhs_ty.to_string(),
                    SkolConstraint::new(mono_tys.iter().cloned(), lhs_ty.clone(), rhs_ty.clone()),
                ));
            } else {
                log::debug!("SkolConstraint::lift: {} is not in the sigs", x);
            }
        }

        cl
    }
}

pub struct ProveConstraint;

impl ProveConstraint {
    pub fn new(pred: Predicate<Ty, TyVar>) -> Constraint {
        QualifierConstraint::prove(pred, TypeSystemInfo::default()).into()
    }
}

pub struct AssumeConstraint;

impl AssumeConstraint {
    pub fn new(pred: Predicate<Ty, TyVar>) -> Constraint {
        QualifierConstraint::assume(pred, TypeSystemInfo::default()).into()
    }
}

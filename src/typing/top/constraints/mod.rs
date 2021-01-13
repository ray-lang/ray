mod satisfiable;
pub mod tree;

pub use satisfiable::*;

use std::{collections::HashSet, iter::FromIterator};

use itertools::Itertools;

use crate::{
    span::Source,
    typing::{
        predicate::TyPredicate,
        ty::{Ty, TyVar},
        ApplySubst, Subst,
    },
};

use super::{
    assumptions::AssumptionSet,
    state::TyEnv,
    traits::{HasFreeVars, PolymorphismInfo},
};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct EqConstraint(Ty, Ty);

impl Into<ConstraintKind> for EqConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Eq(self)
    }
}

impl std::fmt::Debug for EqConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ≡ {}", self.0, self.1)
    }
}

impl EqConstraint {
    pub fn new(t: Ty, u: Ty) -> Constraint {
        Constraint::new(EqConstraint(t, u))
    }

    pub fn lift(aset: &AssumptionSet, env: &TyEnv) -> Vec<(String, Constraint)> {
        let mut cl = vec![];
        for (x, lhs_ty) in env.iter().sorted_by_key(|&(x, _)| x) {
            if let Some(tys) = aset.get(x) {
                for rhs_ty in tys.iter().sorted() {
                    cl.push((
                        rhs_ty.to_string(),
                        EqConstraint::new(lhs_ty.clone(), rhs_ty.clone()),
                    ));
                }
            }
        }

        cl
    }

    pub fn unpack(self) -> (Ty, Ty) {
        (self.0, self.1)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct GenConstraint(Vec<Ty>, TyVar, Ty);

impl Into<ConstraintKind> for GenConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Gen(self)
    }
}

impl std::fmt::Debug for GenConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} := Gen({:?}, {})", self.1, self.0, self.2)
    }
}

impl GenConstraint {
    pub fn new(v: Vec<Ty>, tv: TyVar, t: Ty) -> Constraint {
        Constraint::new(GenConstraint(v, tv, t))
    }

    pub fn unpack(self) -> (Vec<Ty>, TyVar, Ty) {
        (self.0, self.1, self.2)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct InstConstraint(Ty, Ty);

impl Into<ConstraintKind> for InstConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Inst(self)
    }
}

impl std::fmt::Debug for InstConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ≼ {}", self.0, self.1)
    }
}

impl InstConstraint {
    pub fn new(t: Ty, u: Ty) -> Constraint {
        Constraint::new(InstConstraint(t, u))
    }

    pub fn unpack(self) -> (Ty, Ty) {
        (self.0, self.1)
    }

    pub fn lift(aset: &AssumptionSet, sigs: &TyEnv) -> Vec<(String, Constraint)> {
        let mut cl = vec![];
        for (x, tys) in aset.iter().sorted_by_key(|&(x, _)| x) {
            if let Some(rhs_ty) = sigs.get(x) {
                for lhs_ty in tys {
                    cl.push((
                        lhs_ty.to_string(),
                        InstConstraint::new(lhs_ty.clone(), rhs_ty.clone()),
                    ));
                }
            }
        }

        cl
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SkolConstraint(Vec<TyVar>, Ty, Ty);

impl Into<ConstraintKind> for SkolConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Skol(self)
    }
}

impl std::fmt::Debug for SkolConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} ≽{} {}",
            self.1,
            if self.0.len() == 0 {
                str!("∅")
            } else {
                format!("{:?}", self.0)
            },
            self.2
        )
    }
}

impl SkolConstraint {
    pub fn new<I: IntoIterator<Item = TyVar>>(v: I, t: Ty, u: Ty) -> Constraint {
        Constraint::new(SkolConstraint(Vec::from_iter(v), t, u))
    }

    pub fn lift(env: &TyEnv, sigs: &TyEnv, mono_tys: &HashSet<TyVar>) -> Vec<(String, Constraint)> {
        let mut cl = vec![];
        for (x, lhs_ty) in env.iter().sorted_by_key(|&(x, _)| x) {
            if let Some(rhs_ty) = sigs.get(x) {
                cl.push((
                    lhs_ty.to_string(),
                    Constraint::new(SkolConstraint(
                        mono_tys.iter().cloned().collect(),
                        lhs_ty.clone(),
                        rhs_ty.clone(),
                    )),
                ));
            }
        }

        cl
    }

    pub fn unpack(self) -> (Vec<TyVar>, Ty, Ty) {
        (self.0, self.1, self.2)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ImplicitConstraint(Vec<TyVar>, Ty, Ty);

impl Into<ConstraintKind> for ImplicitConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Implicit(self)
    }
}

impl std::fmt::Debug for ImplicitConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} ≤{} {}",
            self.1,
            if self.0.len() == 0 {
                str!("∅")
            } else {
                format!("{:?}", self.0)
            },
            self.2
        )
    }
}

impl ImplicitConstraint {
    pub fn new(vs: Vec<TyVar>, t: Ty, u: Ty) -> Constraint {
        Constraint::new(ImplicitConstraint(vs, t, u))
    }

    pub fn unpack(self) -> (Vec<TyVar>, Ty, Ty) {
        (self.0, self.1, self.2)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ProveConstraint(TyPredicate);

impl Into<ConstraintKind> for ProveConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Prove(self)
    }
}

impl std::fmt::Debug for ProveConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Prove ({})", self.0)
    }
}

impl ProveConstraint {
    pub fn new(q: TyPredicate) -> Constraint {
        Constraint::new(ProveConstraint(q))
    }

    pub fn get_predicate(self) -> TyPredicate {
        self.0
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AssumeConstraint(TyPredicate);

impl Into<ConstraintKind> for AssumeConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Assume(self)
    }
}

impl std::fmt::Debug for AssumeConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Assume ({})", self.0)
    }
}

impl AssumeConstraint {
    pub fn new(q: TyPredicate) -> Constraint {
        Constraint::new(AssumeConstraint(q))
    }

    pub fn get_predicate(self) -> TyPredicate {
        self.0
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ConstraintKind {
    Eq(EqConstraint),
    Gen(GenConstraint),
    Inst(InstConstraint),
    Skol(SkolConstraint),
    Implicit(ImplicitConstraint),
    Prove(ProveConstraint),
    Assume(AssumeConstraint),
}

impl std::fmt::Debug for ConstraintKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintKind::Eq(c) => write!(f, "{:?}", c),
            ConstraintKind::Gen(c) => write!(f, "{:?}", c),
            ConstraintKind::Inst(c) => write!(f, "{:?}", c),
            ConstraintKind::Skol(c) => write!(f, "{:?}", c),
            ConstraintKind::Implicit(c) => write!(f, "{:?}", c),
            ConstraintKind::Prove(c) => write!(f, "{:?}", c),
            ConstraintKind::Assume(c) => write!(f, "{:?}", c),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstraintInfo {
    pub src: Vec<Source>,
}

impl PolymorphismInfo for ConstraintInfo {}

impl ConstraintInfo {
    pub fn new() -> ConstraintInfo {
        ConstraintInfo { src: vec![] }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Constraint {
    pub kind: ConstraintKind,
    pub info: ConstraintInfo,
}

impl std::fmt::Debug for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}

impl HasFreeVars for Constraint {
    fn free_vars(&self) -> HashSet<&TyVar> {
        match &self.kind {
            ConstraintKind::Eq(EqConstraint(s, t)) | ConstraintKind::Inst(InstConstraint(s, t)) => {
                s.free_vars().union(&t.free_vars()).map(|&v| v).collect()
            }
            ConstraintKind::Gen(GenConstraint(m, s, t)) => {
                let mut h = HashSet::new();
                h.insert(s);
                h.extend(m.free_vars());
                h.extend(t.free_vars());
                h
            }
            ConstraintKind::Skol(SkolConstraint(vs, s, t))
            | ConstraintKind::Implicit(ImplicitConstraint(vs, s, t)) => {
                let mut h = HashSet::new();
                h.extend(vs.iter());
                h.extend(s.free_vars());
                h.extend(t.free_vars());
                h
            }
            ConstraintKind::Prove(_) | ConstraintKind::Assume(_) => HashSet::new(),
        }
    }
}

impl HasFreeVars for Vec<Constraint> {
    fn free_vars(&self) -> HashSet<&TyVar> {
        self.iter().flat_map(|c| c.free_vars()).collect()
    }
}

impl HasFreeVars for Vec<(String, Constraint)> {
    fn free_vars(&self) -> HashSet<&TyVar> {
        self.iter().flat_map(|(_, c)| c.free_vars()).collect()
    }
}

impl ApplySubst for Constraint {
    fn apply_subst(self, subst: &Subst) -> Self {
        let info = self.info;
        let kind = match self.kind {
            ConstraintKind::Eq(EqConstraint(s, t)) => {
                EqConstraint(s.apply_subst(subst), t.apply_subst(subst)).into()
            }
            ConstraintKind::Inst(InstConstraint(s, t)) => {
                InstConstraint(s.apply_subst(subst), t.apply_subst(subst)).into()
            }
            ConstraintKind::Gen(GenConstraint(m, s, t)) => GenConstraint(
                m.apply_subst(subst),
                s.apply_subst(subst),
                t.apply_subst(subst),
            )
            .into(),
            ConstraintKind::Skol(SkolConstraint(vs, s, t)) => SkolConstraint(
                vs.apply_subst(subst),
                s.apply_subst(subst),
                t.apply_subst(subst),
            )
            .into(),
            ConstraintKind::Implicit(ImplicitConstraint(vs, s, t)) => ImplicitConstraint(
                vs.apply_subst(subst),
                s.apply_subst(subst),
                t.apply_subst(subst),
            )
            .into(),
            ConstraintKind::Prove(ProveConstraint(p)) => {
                ProveConstraint(p.apply_subst(subst)).into()
            }
            ConstraintKind::Assume(AssumeConstraint(p)) => {
                AssumeConstraint(p.apply_subst(subst)).into()
            }
        };

        Constraint { kind, info }
    }
}

impl Constraint {
    pub fn new<T: Into<ConstraintKind>>(c: T) -> Constraint {
        Constraint {
            kind: c.into(),
            info: ConstraintInfo::new(),
        }
    }

    pub fn with_src(mut self, src: Option<Source>) -> Constraint {
        if let Some(src) = src {
            self.info.src.push(src);
        }
        self
    }

    pub fn with_info(mut self, info: ConstraintInfo) -> Constraint {
        self.info = info;
        self
    }
}

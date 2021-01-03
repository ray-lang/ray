pub mod tree;

use tree::ConstraintTree;

use std::collections::HashSet;

use itertools::Itertools;

use crate::{
    span::Span,
    typing::{
        ty::{Ty, TyVar},
        ApplySubst, Subst,
    },
};

use self::tree::{AttachTree, NodeTree, ReceiverTree};

use super::{
    assumptions::AssumptionSet,
    binding::{BindingGroup, BindingGroupAnalysis},
    state::{TyEnv, TyVarFactory},
    traits::{HasFreeVars, PolymorphismInfo},
};

pub trait CollectConstraints {
    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Ty, AssumptionSet, ConstraintTree);

    fn pattern_var(&self, var: &String, tf: &mut TyVarFactory) -> (Ty, TyEnv, ConstraintTree) {
        let mut env = TyEnv::new();
        let tv = tf.next();
        env.insert(var.clone(), Ty::Var(tv.clone()));
        let ct = ReceiverTree::new(var.to_string());
        (Ty::Var(tv), env, ct)
    }

    fn decl_var<T: CollectConstraints>(
        &self,
        var: &String,
        rhs: &T,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (BindingGroup, TyEnv) {
        let (lhs_ty, env, ct1) = self.pattern_var(var, tf);
        let (rhs_ty, a, ct2) = self.collect_rhs(rhs, mono_tys, tf);
        let c = Constraint::new(EqConstraint(lhs_ty, rhs_ty));
        let bg = BindingGroup::new(env, a, AttachTree::new(c, NodeTree::new(vec![ct1, ct2])));

        (bg, TyEnv::new())
    }

    fn collect_rhs<T: CollectConstraints>(
        &self,
        ex: &T,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Ty, AssumptionSet, ConstraintTree) {
        let (ty, a, ct) = ex.collect_constraints(mono_tys, tf);
        let bg = BindingGroup::new(TyEnv::new(), a, ct);
        let defs = TyEnv::new();
        let mut bga = BindingGroupAnalysis::new(vec![bg], &defs, tf, mono_tys);
        let (_, a, ct) = bga.analyze();
        (ty, a, ct)
    }
}

impl<T: CollectConstraints> CollectConstraints for Box<T> {
    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Ty, AssumptionSet, ConstraintTree) {
        self.as_ref().collect_constraints(mono_tys, tf)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct EqConstraint(pub Ty, pub Ty);

impl Into<ConstraintKind> for EqConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Eq(self)
    }
}

impl std::fmt::Debug for EqConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} == {}", self.0, self.1)
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
                        x.clone(),
                        Constraint::new(EqConstraint(lhs_ty.clone(), rhs_ty.clone())),
                    ));
                }
            }
        }

        cl
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct GenConstraint(pub Vec<Ty>, pub TyVar, pub Ty);

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
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct InstConstraint(pub Ty, pub Ty);

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
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SkolConstraint(pub Vec<TyVar>, pub Ty, pub Ty);

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
    pub fn lift(env: &TyEnv, defs: &TyEnv, mono_tys: &HashSet<TyVar>) -> Vec<(String, Constraint)> {
        let mut cl = vec![];
        for (x, lhs_ty) in env.iter().sorted_by_key(|&(x, _)| x) {
            if let Some(rhs_ty) = defs.get(x) {
                cl.push((
                    x.clone(),
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
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ImplicitConstraint(pub Vec<TyVar>, pub Ty, pub Ty);

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

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ConstraintKind {
    Eq(EqConstraint),
    Gen(GenConstraint),
    Inst(InstConstraint),
    Skol(SkolConstraint),
    Implicit(ImplicitConstraint),
}

impl std::fmt::Debug for ConstraintKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintKind::Eq(c) => write!(f, "{:?}", c),
            ConstraintKind::Gen(c) => write!(f, "{:?}", c),
            ConstraintKind::Inst(c) => write!(f, "{:?}", c),
            ConstraintKind::Skol(c) => write!(f, "{:?}", c),
            ConstraintKind::Implicit(c) => write!(f, "{:?}", c),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstraintInfo {
    pub span: Option<Span>,
}

impl PolymorphismInfo for ConstraintInfo {}

impl ConstraintInfo {
    pub fn new() -> ConstraintInfo {
        ConstraintInfo { span: None }
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
        println!("apply subst to constraint (before): {:?}", self);
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
        };

        println!("apply subst to constraint (after): {:?}", kind);

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

    pub fn syntax(&self) -> String {
        todo!()
    }

    pub fn semantics<F: Fn() -> bool>(&self) -> F {
        todo!()
    }
}

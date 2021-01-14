use std::collections::HashSet;

use crate::{
    span::Source,
    typing::ty::{Ty, TyVar},
};

use super::{
    assumptions::AssumptionSet,
    binding::BindingGroup,
    constraints::{
        tree::{AttachTree, ConstraintTree, NodeTree, ReceiverTree},
        EqConstraint,
    },
    state::{TyEnv, TyVarFactory},
    traits::HasType,
};

pub trait CollectPatterns {
    fn collect_patterns(&self, tf: &mut TyVarFactory) -> (Ty, TyEnv, ConstraintTree);
}

impl CollectPatterns for String {
    fn collect_patterns(&self, tf: &mut TyVarFactory) -> (Ty, TyEnv, ConstraintTree) {
        let mut env = TyEnv::new();
        let tv = tf.next();
        env.insert(self.clone(), Ty::Var(tv.clone()));
        let ct = ReceiverTree::new(tv.to_string());
        (Ty::Var(tv), env, ct)
    }
}

pub trait CollectDeclarations
where
    Self: Sized,
{
    fn collect_decls(
        self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Self, BindingGroup, TyEnv);
}

impl<V, R> CollectDeclarations for (V, R, Option<Source>)
where
    Self: Sized,
    V: CollectPatterns + std::fmt::Debug,
    R: HasType + CollectConstraints + std::fmt::Debug,
{
    fn collect_decls(
        self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Self, BindingGroup, TyEnv) {
        let (var, rhs, src) = self;

        // E,Tc1 ⊢p p : τ1
        let (lhs_ty, env, ct1) = var.collect_patterns(tf);

        // ⟨M⟩, A, Tc2 ⊢e rhs : τ2
        let (rhs, a, ct2) = rhs.collect_constraints(mono_tys, tf);
        let rhs_ty = rhs.get_type();

        // c = (τ1 ≡ τ2)
        let c = EqConstraint::new(lhs_ty, rhs_ty).with_src(src.clone());

        // B = (E, A, c ▹ [Ct1, Ct2])
        let bg = BindingGroup::new(env, a, AttachTree::new(c, NodeTree::new(vec![ct1, ct2])))
            .with_src(src.clone());

        ((var, rhs, src), bg, TyEnv::new())
    }
}

impl<V, R> CollectDeclarations for (V, R)
where
    V: CollectPatterns + std::fmt::Debug,
    R: HasType + CollectConstraints + std::fmt::Debug,
{
    fn collect_decls(
        self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Self, BindingGroup, TyEnv) {
        let (var, rhs) = self;
        let ((var, rhs, _), bg, env) = (var, rhs, None).collect_decls(mono_tys, tf);
        ((var, rhs), bg, env)
    }
}

pub trait CollectConstraints
where
    Self: Sized,
{
    fn collect_constraints(
        self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Self, AssumptionSet, ConstraintTree);
}

impl<T> CollectConstraints for Box<T>
where
    Self: Sized,
    T: CollectConstraints,
{
    fn collect_constraints(
        self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Self, AssumptionSet, ConstraintTree) {
        let (b, a, c) = (*self).collect_constraints(mono_tys, tf);
        (Box::new(b), a, c)
    }
}

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

pub trait CollectDeclarations {
    fn collect_decls(
        &self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (BindingGroup, TyEnv);
}

impl<V, R> CollectDeclarations for (&V, &R, Option<&Source>)
where
    V: CollectPatterns + std::fmt::Debug,
    R: CollectConstraints + std::fmt::Debug,
{
    fn collect_decls(
        &self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (BindingGroup, TyEnv) {
        let &(var, rhs, src) = self;
        println!("collect_decls: {:?}, {:?}, {:?}", var, rhs, src);

        // E,Tc1 ⊢p p : τ1
        let (lhs_ty, env, ct1) = var.collect_patterns(tf);

        // ⟨M⟩, A, Tc2 ⊢e rhs : τ2
        let (rhs_ty, a, ct2) = rhs.collect_constraints(mono_tys, tf);

        // c = (τ1 ≡ τ2)
        let c = EqConstraint::new(lhs_ty, rhs_ty).with_src(src.cloned());

        // B = (E, A, c ▹ [Ct1, Ct2])
        let bg = BindingGroup::new(env, a, AttachTree::new(c, NodeTree::new(vec![ct1, ct2])))
            .with_src(src.cloned());

        (bg, TyEnv::new())
    }
}

impl<V, R> CollectDeclarations for (&V, &R)
where
    V: CollectPatterns + std::fmt::Debug,
    R: CollectConstraints + std::fmt::Debug,
{
    fn collect_decls(
        &self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (BindingGroup, TyEnv) {
        let &(var, rhs) = self;
        (var, rhs, None).collect_decls(mono_tys, tf)
    }
}

pub trait CollectConstraints {
    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Ty, AssumptionSet, ConstraintTree);
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

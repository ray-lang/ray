use std::collections::HashSet;

use crate::{
    ast::{Path, SourceInfo},
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
        let path = Path::from(self.clone());
        path.collect_patterns(tf)
    }
}

impl CollectPatterns for Path {
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
    type Output;

    fn collect_decls(
        self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Self::Output, BindingGroup, TyEnv);
}

impl<V, A, B> CollectDeclarations for (V, A, SourceInfo)
where
    Self: Sized,
    V: CollectPatterns + std::fmt::Debug,
    A: CollectConstraints<Output = B> + std::fmt::Debug,
    B: HasType,
{
    type Output = (V, B, SourceInfo);

    fn collect_decls(
        self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Self::Output, BindingGroup, TyEnv) {
        let (var, rhs, src) = self;

        // E,Tc1 ⊢p p : τ1
        let (lhs_ty, env, ct1) = var.collect_patterns(tf);

        // ⟨M⟩, A, Tc2 ⊢e rhs : τ2
        let (rhs, a, ct2) = rhs.collect_constraints(mono_tys, tf);
        let rhs_ty = rhs.ty();

        // c = (τ1 ≡ τ2)
        let c = EqConstraint::new(lhs_ty, rhs_ty).with_src(src.clone());

        // B = (E, A, c ▹ [Ct1, Ct2])
        let bg = BindingGroup::new(env, a, AttachTree::new(c, NodeTree::new(vec![ct1, ct2])))
            .with_src(src.clone());

        ((var, rhs, src), bg, TyEnv::new())
    }
}

// impl<V, A, B> CollectDeclarations for (V, A)
// where
//     Self: Sized,
//     V: CollectPatterns + std::fmt::Debug,
//     A: HasType + CollectConstraints<Output = B> + std::fmt::Debug,
// {
//     type Output = (V, B);

//     fn collect_decls(
//         self,
//         mono_tys: &HashSet<TyVar>,
//         tf: &mut TyVarFactory,
//     ) -> (Self::Output, BindingGroup, TyEnv) {
//         let (var, rhs) = self;
//         let x: (V, A, Option<Source>) = (var, rhs, None);
//         let ((var, rhs, _), bg, env) = x.collect_decls(mono_tys, tf);
//         ((var, rhs), bg, env)
//     }
// }

pub trait CollectConstraints
where
    Self: Sized,
{
    type Output;

    fn collect_constraints(
        self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Self::Output, AssumptionSet, ConstraintTree);
}

impl<T, U> CollectConstraints for Box<T>
where
    Self: Sized,
    T: CollectConstraints<Output = U>,
{
    type Output = Box<U>;

    fn collect_constraints(
        self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let (b, a, c) = (*self).collect_constraints(mono_tys, tf);
        (Box::new(b), a, c)
    }
}

// impl<T> CollectConstraints for Node<Expr<SourceInfo>, SourceInfo>
// where
//     (Expr<SourceInfo>, SourceInfo): CollectConstraints<Output = (Expr<T>, T)>,
//     T: std::fmt::Debug + Clone + PartialEq + Eq + HasSource + HasDoc + HasType,
// {
//     type Output = Node<Expr<T>, T>;

//     fn collect_constraints(
//         self,
//         mono_tys: &HashSet<TyVar>,
//         tf: &mut TyVarFactory,
//     ) -> (Self::Output, AssumptionSet, ConstraintTree) {
//         let id = self.id;
//         let ((value, info), aset, ct) = (self.value, self.info).collect_constraints(mono_tys, tf);
//         (Node { id, value, info }, aset, ct)
//     }
// }

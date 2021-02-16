use std::collections::HashSet;

use crate::{
    ast::{Node, Path, SourceInfo},
    span::{Source, SourceMap},
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
    TyCtx,
};

pub trait CollectPatterns {
    fn collect_patterns(&self, srcmap: &SourceMap, tcx: &mut TyCtx) -> (Ty, TyEnv, ConstraintTree);
}

impl CollectPatterns for String {
    fn collect_patterns(&self, srcmap: &SourceMap, tcx: &mut TyCtx) -> (Ty, TyEnv, ConstraintTree) {
        let path = Path::from(self.clone());
        path.collect_patterns(srcmap, tcx)
    }
}

impl CollectPatterns for Path {
    fn collect_patterns(&self, srcmap: &SourceMap, tcx: &mut TyCtx) -> (Ty, TyEnv, ConstraintTree) {
        let mut env = TyEnv::new();
        let tv = tcx.tf().next();
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
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (BindingGroup, TyEnv);
}

impl<V, T> CollectDeclarations for (&V, &Node<T>, &Source)
where
    Self: Sized,
    V: CollectPatterns,
    Node<T>: CollectConstraints<Output = Ty>,
{
    fn collect_decls(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (BindingGroup, TyEnv) {
        let &(var, rhs, src) = self;

        // E,Tc1 ⊢p p : τ1
        let (lhs_ty, env, ct1) = var.collect_patterns(srcmap, tcx);

        // ⟨M⟩, A, Tc2 ⊢e rhs : τ2
        let (rhs_ty, a, ct2) = rhs.collect_constraints(mono_tys, srcmap, tcx);

        // c = (τ1 ≡ τ2)
        let c = EqConstraint::new(lhs_ty, rhs_ty).with_src(src.clone());

        // B = (E, A, c ▹ [Ct1, Ct2])
        let bg = BindingGroup::new(env, a, AttachTree::new(c, NodeTree::new(vec![ct1, ct2])))
            .with_src(src.clone());

        (bg, TyEnv::new())
    }
}

pub trait CollectConstraints {
    type Output;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree);
}

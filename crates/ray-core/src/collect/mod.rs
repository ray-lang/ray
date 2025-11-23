mod ast;

use std::collections::HashSet;

use ray_typing::{
    TyCtx,
    assumptions::AssumptionSet,
    bound_names::BoundNames,
    constraints::{
        EqConstraint,
        tree::{AttachTree, ConstraintTree, NodeTree, ReceiverTree},
    },
    state::{Env, SchemeEnv, TyEnv},
    ty::{Ty, TyVar},
};
use ray_shared::{collections::namecontext::NameContext, pathlib::Path, span::Source};

use crate::{ast::Node, bga::BindingGroup, sourcemap::SourceMap};

pub struct CollectCtx<'a> {
    pub mono_tys: &'a HashSet<TyVar>,
    pub srcmap: &'a SourceMap,
    pub tcx: &'a mut TyCtx,
    pub ncx: &'a mut NameContext,
    pub defs: SchemeEnv,
    pub new_defs: &'a mut SchemeEnv,
    pub bound_names: &'a mut BoundNames,
}

impl CollectCtx<'_> {
    pub fn with_ctx<F, A>(&mut self, mut f: F) -> A
    where
        F: FnMut(&mut CollectCtx) -> A,
    {
        let mut ctx = CollectCtx {
            mono_tys: self.mono_tys,
            srcmap: self.srcmap,
            tcx: self.tcx,
            ncx: self.ncx,
            defs: self.defs.clone(),
            new_defs: self.new_defs,
            bound_names: self.bound_names,
        };

        f(&mut ctx)
    }

    pub fn with_frame<F, A>(&mut self, f: F) -> A
    where
        F: FnOnce(&mut CollectCtx) -> A,
    {
        self.bound_names.enter();
        let result = f(self);
        self.bound_names.exit();
        result
    }
}

pub trait CollectPatterns {
    fn collect_patterns(&self, ctx: &mut CollectCtx) -> (Ty, TyEnv, ConstraintTree);
}

impl CollectPatterns for String {
    fn collect_patterns(&self, ctx: &mut CollectCtx) -> (Ty, TyEnv, ConstraintTree) {
        let path = Path::from(self.clone());
        path.collect_patterns(ctx)
    }
}

impl CollectPatterns for Path {
    fn collect_patterns(&self, ctx: &mut CollectCtx) -> (Ty, TyEnv, ConstraintTree) {
        let mut env = Env::new();
        let tv = ctx.tcx.tf().next();
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

    fn collect_decls(&self, ctx: &mut CollectCtx) -> Self::Output;
}

impl<V, T> CollectDeclarations for (&V, &Node<T>, &Source)
where
    Self: Sized,
    V: CollectPatterns,
    Node<T>: CollectConstraints<Output = Ty>,
{
    type Output = (Ty, BindingGroup, SchemeEnv);

    fn collect_decls(&self, ctx: &mut CollectCtx) -> Self::Output {
        let &(var, rhs, src) = self;

        // E,Tc1 ⊢p p : τ1
        let (lhs_ty, env, ct1) = var.collect_patterns(ctx);

        let lhs_names = env.keys().map(|path| path.to_string()).collect::<Vec<_>>();
        log::debug!(
            "collect_decls: lhs_names={:?} lhs_ty={} rhs_id={}",
            lhs_names,
            lhs_ty,
            rhs.id
        );

        // ⟨M⟩, A, Tc2 ⊢e rhs : τ2
        let (rhs_ty, a, ct2) = rhs.collect_constraints(ctx);

        // c = (τ1 ≡ τ2)
        let mut c = EqConstraint::new(lhs_ty.clone(), rhs_ty);
        c.info_mut().with_src(src.clone());
        log::debug!("collect_decls: eq_constraint={}", c);

        // B = (E, A, c ▹ [Ct1, Ct2])
        let bg = BindingGroup::new(env, a, AttachTree::new(c, NodeTree::new(vec![ct1, ct2])))
            .with_src(src.clone());

        (lhs_ty, bg, SchemeEnv::new())
    }
}

pub trait CollectConstraints {
    type Output;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree);
}

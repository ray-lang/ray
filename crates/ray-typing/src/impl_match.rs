use std::collections::HashSet;

use ray_shared::ty::{Ty, TyVar};

use crate::{
    constraints::{ClassPredicate, Constraint, Predicate},
    context::MetaAllocator,
    info::TypeSystemInfo,
    types::{ImplKind, ImplTy, Subst, Substitutable as _},
    unify::unify,
};

/// Result of matching an impl head against a class predicate.
///
/// This captures the substitutions and fresh metas created when instantiating
/// schema variables for a candidate impl and unifying its head with the wanted
/// predicate. Callers can use the stored substitutions to instantiate the impl
/// predicates and decide which trial metas to keep or discard.
#[derive(Debug)]
pub struct ImplHeadMatch {
    pub base_ty_head: Ty,
    pub ty_args_head: Vec<Ty>,
    pub trial_subst: Subst,
    pub schema_subst: Subst,
    pub trial_metas: Vec<TyVar>,
}

/// Try to match an impl head with a wanted class predicate.
///
/// This:
/// - Instantiates schema variables with fresh metas (via `MetaAllocator`).
/// - Unifies the receiver and type arguments.
/// - Returns the trial substitution, schema substitution, and trial metas.
/// - Returns `None` on any mismatch (and reuses allocated metas).
pub fn match_impl_head(
    wanted: &ClassPredicate,
    impl_ty: &ImplTy,
    subst: &Subst,
    meta_alloc: &mut impl MetaAllocator,
    info: &TypeSystemInfo,
) -> Option<ImplHeadMatch> {
    let ImplKind::Trait {
        base_ty, ty_args, ..
    } = &impl_ty.kind
    else {
        return None;
    };

    if wanted.args.is_empty() || ty_args.len() != wanted.args.len() - 1 {
        return None;
    }

    let base_ty_head = base_ty.clone();
    let ty_args_head = ty_args.clone();

    // Instantiate schema variables with fresh metas so the impl head can be
    // unified against the wanted predicate without leaking schema vars.
    let mut vars = HashSet::new();
    impl_ty.free_ty_vars(&mut vars);
    let schema_vars = vars
        .iter()
        .filter(|var| var.is_schema())
        .cloned()
        .collect::<Vec<_>>();

    let mut schema_subst = Subst::new();
    let mut trial_metas = Vec::new();
    for var in schema_vars.iter() {
        let meta = meta_alloc.fresh_meta();
        if let Ty::Var(v) = &meta {
            trial_metas.push(v.clone());
        }
        schema_subst.insert(var.clone(), meta);
    }

    let mut base_ty = base_ty.clone();
    let mut ty_args = ty_args.clone();
    base_ty.apply_subst(&schema_subst);
    ty_args.apply_subst(&schema_subst);

    let mut args = wanted.args.clone();
    args.apply_subst(subst);

    let recv_ty = &args[0];
    let arg_tys = &args[1..];

    let mut trial_subst = subst.clone();

    // Unify receiver type with the impl's base type.
    log::debug!(
        "[match_impl_head] recv_ty = {}, base_ty = {}",
        recv_ty,
        base_ty
    );
    match unify(recv_ty, &base_ty, &trial_subst, info) {
        Ok(new_subst) => {
            trial_subst.union(new_subst);
        }
        Err(_) => {
            meta_alloc.reuse_metas(trial_metas);
            return None;
        }
    };

    // Unify the remaining arguments with the impl's type arguments.
    for (wanted_arg, impl_arg) in arg_tys.iter().zip(&ty_args) {
        match unify(wanted_arg, impl_arg, &trial_subst, info) {
            Ok(new_subst) => {
                trial_subst.union(new_subst);
            }
            Err(_) => {
                meta_alloc.reuse_metas(trial_metas);
                return None;
            }
        }
    }

    Some(ImplHeadMatch {
        base_ty_head,
        ty_args_head,
        trial_subst,
        schema_subst,
        trial_metas,
    })
}

pub fn instantiate_impl_predicates(
    impl_ty: &ImplTy,
    schema_subst: &Subst,
    trial_subst: &Subst,
) -> Vec<Predicate> {
    // The impl's predicates are written in terms of the impl's schema variables
    // (e.g. `UnsignedInt['a]`). Those schema variables must be instantiated to
    // the same fresh metas as the impl head (base_ty/ty_args) before we can
    // attempt to solve them.
    let mut instantiated = Vec::with_capacity(impl_ty.predicates.len());
    for pred in &impl_ty.predicates {
        let mut p = pred.clone();
        p.apply_subst(schema_subst);
        p.apply_subst(trial_subst);
        instantiated.push(p);
    }
    instantiated
}

/// Collect the meta-variable roots used to decide which trial metas survive.
///
/// Roots include metas from the wanted predicate, givens, and the impl's own
/// predicates after applying the trial substitution. This mirrors the solver's
/// reachability rules for keeping newly-created metas.
pub fn collect_meta_roots(
    wanted: &ClassPredicate,
    givens: &[Constraint],
    impl_ty: &ImplTy,
    trial_subst: &Subst,
) -> Vec<TyVar> {
    // Metas that existed before any probing begins. We use these as the
    // reachability roots to decide which trial metas must be kept.
    let mut meta_roots_set: HashSet<_> = HashSet::new();

    for ty in &wanted.args {
        ty.free_ty_vars(&mut meta_roots_set);
    }
    for g in givens {
        g.free_ty_vars(&mut meta_roots_set);
    }

    // Also treat residuals as roots (future-proofing): if they mention
    // a trial meta, that meta must survive.
    for pred in &impl_ty.predicates {
        let mut p = pred.clone();
        p.apply_subst(trial_subst);
        p.free_ty_vars(&mut meta_roots_set);
    }

    meta_roots_set.into_iter().filter(|v| v.is_meta()).collect()
}

/// Determine which trial metas can be discarded after a successful probe.
///
/// Any trial meta reachable from the provided roots via `trial_subst` must be
/// kept. The remaining trial metas are safe to recycle.
pub fn collect_discarded_trial_metas(
    meta_roots: &[TyVar],
    trial_metas: &[TyVar],
    trial_subst: &Subst,
) -> Vec<TyVar> {
    let mut visited: HashSet<_> = HashSet::new();
    let mut work: Vec<_> = meta_roots.to_vec();

    while let Some(meta) = work.pop() {
        if visited.contains(&meta) {
            continue;
        }

        visited.insert(meta.clone());
        if let Some(ty) = trial_subst.get(&meta) {
            let mut vars = HashSet::new();
            ty.free_ty_vars(&mut vars);
            work.extend(vars.into_iter().filter(|v| v.is_meta()));
        }
    }

    trial_metas
        .iter()
        .cloned()
        .filter(|m| !visited.contains(m))
        .collect()
}

/// Compute the delta substitution to commit after a successful probe.
///
/// Only metas that existed before probing (`meta_roots`) are considered. The
/// commit substitution includes only bindings that changed after applying the
/// trial substitution.
pub fn commit_trial_subst(meta_roots: &[TyVar], trial_subst: &Subst, subst: &Subst) -> Subst {
    let mut commit_subst = Subst::new();
    for meta in meta_roots {
        if let Some(rhs) = trial_subst.get(meta) {
            let mut rhs_norm = rhs.clone();
            rhs_norm.apply_subst(trial_subst);

            let mut changed = true;
            if let Some(old_rhs) = subst.get(meta) {
                let mut old_rhs_norm = old_rhs.clone();
                old_rhs_norm.apply_subst(subst);
                changed = old_rhs_norm != rhs_norm;
            }

            if changed {
                commit_subst.insert(meta.clone(), rhs_norm);
            }
        }
    }

    commit_subst
}

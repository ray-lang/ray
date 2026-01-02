//! Generalization pass for the type system.
//!
//! This implements the "from metas to schemes" step described in
//! docs/type-system.md Section 3.4. After constraint solving (including
//! defaulting), we walk the types associated with each binding in a binding
//! group and decide which meta type variables become quantified `forall`
//! variables in the binding's `TyScheme`.
//!
//! The rough shape is:
//! - For each binding in the group, take its mono type from TypeContext.
//! - Compute the set of candidate metas that appear in that type.
//! - Subtract metas that:
//!   - are not truly flexible anymore (unified with rigids/skolems), or
//!   - should remain monomorphic according to the value restriction /
//!     will_be_generalized predicate, or
//!   - appear in residual constraints that must stay attached to the scheme.
//! - The remaining metas become the `vars` of the scheme, and we apply a
//!   closing substitution so that the scheme's body contains only rigid
//!   variables in `vars` plus any non-generalized metas.
//!
use std::collections::HashSet;

use ray_shared::{
    node_id::NodeId,
    ty::{Ty, TyVar},
};

use crate::{
    ModuleInput,
    binding_groups::BindingId,
    constraints::{Constraint, ConstraintKind, Predicate},
    context::{ExprKind, SolverContext},
    types::{Subst, Substitutable as _, TyScheme},
};

/// Result of generalizing a single binding group.
pub struct GeneralizationResult {
    /// Updated schemes for each binding in the group, after generalization.
    pub schemes: Vec<(BindingId, TyScheme)>,
    /// Closing substitution applied during generalization. In many cases this
    /// will be empty; it is exposed here so that callers can update any
    /// cached types if necessary.
    pub closing_subst: Subst,
    /// Residual constraints that were not turned into qualifiers for any
    /// scheme inside this group
    pub residuals: Vec<Constraint>,
}

/// Generalize the types of bindings in a binding group after solving.
///
/// Inputs:
/// - `ctx`: the type context containing mono types for expressions and
///   existing `TyScheme`s for bindings (typically with empty `vars`).
/// - `group`: the binding group whose bindings we are generalizing.
/// - `residuals`: any residual constraints that remain after solving and
///   defaulting; these may restrict which metas can be generalized.
/// - `subst`: the final substitution produced by unification / goal solving.
///
/// This walks each binding, computes the set of generalizable metas per
/// Section 3.4 (in a simplified form for now), and returns updated schemes.
pub fn generalize_group(
    module: &ModuleInput,
    ctx: &SolverContext,
    bindings: &[BindingId],
    global_metas: &[TyVar],
    residuals: Vec<Constraint>,
    subst: &Subst,
) -> GeneralizationResult {
    let mut schemes = Vec::new();
    let mut consumed = HashSet::new();
    let mut closing_subst = Subst::new();

    // Collect all type variables that still appear in residual constraints.
    // Any meta variable that occurs in residuals must not be generalized,
    // since its obligations are not yet discharged (Section 3.4).
    let mut vars_in_residuals: HashSet<TyVar> = HashSet::new();
    for constraint in residuals.iter() {
        if matches!(constraint.kind, ConstraintKind::Class(_)) {
            // Class residuals become qualifiers; their type variables
            // should not block generalization.
            continue;
        }

        constraint.free_ty_vars(&mut vars_in_residuals);
    }

    for binding_id in bindings {
        if let Some(scheme) = ctx.binding_schemes.get(binding_id) {
            // If this binding already has a non-trivial scheme (e.g. from an
            // annotated function signature), we treat that scheme as the
            // source of truth for its quantifiers and qualifiers. In that
            // case we only apply the final substitution so the scheme's
            // body and qualifiers reflect the solved types, but we do not
            // attempt to infer new quantified variables.
            let has_annotated_scheme = ctx.is_explicitly_annotated(binding_id)
                || !scheme.vars.is_empty()
                || !scheme.qualifiers.is_empty();

            // Enforce the value restriction: only bindings whose RHS is a
            // syntactic value are eligible for generalization.
            let is_value = module
                .binding_root_expr(*binding_id)
                .map(|root| is_syntactic_value_expr(module, root))
                .unwrap_or(false);

            // Start from the scheme's type with the final substitution
            // applied, so we only see the solved shape here.
            let mut instantiated = scheme.clone();
            instantiated.apply_subst(subst);

            if has_annotated_scheme {
                schemes.push((*binding_id, instantiated));
                continue;
            }

            // Collect type variables that still appear free in the binding's
            // type. Generalization decisions for vars and qualifiers are
            // made relative to the binding's type, not vars that appear only
            // in constraints.
            let mut free_in_ty: HashSet<TyVar> = HashSet::new();
            instantiated.ty.free_ty_vars(&mut free_in_ty);

            // If any meta variable in this binding's type still appears in
            // residual constraints, treat the binding as non-generalizable.
            let has_residual_meta = free_in_ty
                .iter()
                .any(|v| v.is_meta() && vars_in_residuals.contains(v) && !global_metas.contains(v));

            if has_residual_meta || !is_value {
                schemes.push((*binding_id, TyScheme::from_mono(instantiated.ty)));
                continue;
            }

            // Remaining meta variables (not mentioned in residuals) are
            // candidates for generalization.
            let mut metas: Vec<TyVar> =
                free_in_ty.iter().filter(|v| v.is_meta()).cloned().collect();
            metas.sort();

            // Rename each meta class to a fresh schema variable name and
            // record the mapping in the closing substitution.
            let mut vars: Vec<TyVar> = Vec::with_capacity(metas.len());
            let mut local_closing: Subst = Subst::new();
            {
                let mut allocator = ctx.schema_allocator_mut();
                for old in metas {
                    // Map the old meta class name to the new schema variable so
                    // that the scheme body uses rigid quantified variables rather
                    // than solver metas.
                    let new_var = allocator.alloc();
                    local_closing.insert(old.clone(), Ty::Var(new_var.clone()));
                    vars.push(new_var);
                }
            }

            let mut qualifiers: Vec<Predicate> = Vec::new();
            for (idx, c) in residuals.iter().enumerate() {
                if matches!(c.kind, ConstraintKind::Eq(_)) {
                    continue;
                }

                let mut pred_vars = HashSet::new();
                c.free_ty_vars(&mut pred_vars);

                if pred_vars.iter().any(|v| free_in_ty.contains(v)) {
                    let pred = c.to_predicate().expect("predicate from constraint");
                    qualifiers.push(pred);
                    consumed.insert(idx);
                }
            }

            instantiated.ty.apply_subst(&local_closing);
            qualifiers.apply_subst(&local_closing);

            let generalized = TyScheme {
                vars,
                qualifiers,
                ty: instantiated.ty,
            };

            log::debug!(
                "[generalize] scheme = {}, generalized = {}",
                scheme,
                generalized
            );
            closing_subst.extend(local_closing);
            schemes.push((*binding_id, generalized));
        }
    }

    // collect all the residuals that were not consumed
    let residuals: Vec<_> = residuals
        .into_iter()
        .enumerate()
        .filter_map(|(idx, c)| {
            if !consumed.contains(&idx) {
                Some(c)
            } else {
                None
            }
        })
        .collect();

    log::debug!("[generalize] closing_subst = {}", closing_subst);
    GeneralizationResult {
        schemes,
        closing_subst,
        residuals,
    }
}

/// Approximate `is_syntactic_value` from Section 3.4 using the expression
/// kinds available in `ModuleInput`.
fn is_syntactic_value_expr(module: &ModuleInput, expr: NodeId) -> bool {
    match module.expr_kind(expr) {
        Some(ExprKind::Closure { .. }) | Some(ExprKind::Function { .. }) => true,

        Some(ExprKind::Some { expr: inner }) => is_syntactic_value_expr(module, *inner),

        // Other expression forms may become values later (e.g. function
        // literals) once they are lowered into the internal expression kinds.
        _ => false,
    }
}

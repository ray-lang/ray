// Defaulting pass for the type system.
// This runs late in the pipeline to fill in unconstrained metas, as
// described in docs/type-system.md (Section 8).
//
// IMPORTANT: defaulting must NOT introduce new type errors; it is only
// allowed to resolve otherwise unconstrained meta variables in a way that
// does not change which programs type-check. Ambiguity reporting is a
// separate concern handled in the error model (Section 9).

use std::collections::{BTreeMap, HashMap, HashSet};

use ray_shared::node_id::NodeId;

use crate::ModuleInput;
use crate::binding_groups::BindingGroup;
use crate::constraints::{Constraint, ConstraintKind};
use crate::context::{ExprKind, SolverContext};
use crate::env::GlobalEnv;
use crate::goal_solver::solve_constraints;
use crate::types::{Subst, Substitutable as _, Ty, TyVar};
use crate::unify::unify;

/// Outcome of attempting to default a single type-variable class `α`.
#[derive(Clone, Debug)]
pub enum DefaultingOutcomeKind {
    /// Successfully defaulted `α` to `default_ty`.
    Succeeded,
    /// `α` is not flexible (e.g. unified with a rigid/skolem); cannot be defaulted.
    RejectedRigid,
    /// `α` will be generalized into a forall-variable for some binding; cannot be defaulted.
    RejectedPoly,
    /// Adding `α == default_ty` makes the predicate cluster unsatisfiable.
    RejectedUnsat { blocking_preds: Vec<Constraint> },
    /// Multiple viable defaults; do not guess.
    RejectedAmbiguous { candidates: Vec<Ty> },
}

#[derive(Clone, Debug)]
pub struct DefaultingOutcome {
    pub var: TyVar,
    pub default_ty: Ty,
    pub kind: DefaultingOutcomeKind,
}

#[derive(Clone, Debug, Default)]
pub struct DefaultingLog {
    pub entries: Vec<DefaultingOutcome>,
}

/// Result of the defaulting pass.
///
/// - `subst` is the (potentially) updated substitution after applying any
///   defaulting steps.
/// - `residuals` are the remaining constraints after defaulting; in the full
///   implementation this may be smaller than the input residual set.
/// - `log` records decisions for diagnostics (Section 8.3).
pub struct DefaultingResult {
    pub subst: Subst,
    pub residuals: Vec<Constraint>,
    pub log: DefaultingLog,
}

/// Apply defaulting to the types tracked in the given type context and the
/// residual constraints for a binding group.
///
/// This follows the high-level algorithm from Section 8:
/// - Group residual predicates by flexible type-variable class `α` that
///   appears as a receiver in defaultable traits.
/// - For each such `α`, evaluate candidate defaults and commit when there is
///   a unique viable default.
/// - Record all decisions in a `DefaultingLog`.
pub fn apply_defaulting(
    module: &ModuleInput,
    ctx: &mut SolverContext,
    group: &BindingGroup,
    global_env: &GlobalEnv,
    residuals: Vec<Constraint>,
    subst: &Subst,
) -> DefaultingResult {
    let mut log = DefaultingLog::default();
    let mut current_subst = subst.clone();

    // Step 1: find defaultable type-variable classes α that appear as
    // receivers in residual class predicates from traits with defaults.
    let defaultable_classes = find_defaultable_classes(&residuals, global_env, &current_subst);

    // Step 2: cluster predicates by mentions of each α.
    let clusters = group_predicates_by_class(&residuals, &defaultable_classes);

    for (alpha, preds_alpha) in clusters {
        // Skip classes that are no longer flexible.
        if !is_flexible(&alpha, &current_subst) {
            log.entries.push(DefaultingOutcome {
                var: alpha.clone(),
                default_ty: Ty::Any,
                kind: DefaultingOutcomeKind::RejectedRigid,
            });
            continue;
        }

        // Skip classes that will be generalized into schemes according to
        // the value restriction (Section 3.4): if `alpha` appears as a free
        // meta in the type of an eligible binding in this group, we do not
        // default it.
        if will_be_generalized(&alpha, module, group, ctx, &current_subst) {
            log.entries.push(DefaultingOutcome {
                var: alpha.clone(),
                default_ty: Ty::Any,
                kind: DefaultingOutcomeKind::RejectedPoly,
            });
            continue;
        }

        // Step 4: collect candidate defaults from all predicates C[alpha, …]
        // whose trait C has default(T_default). We keep the originating
        // constraint so we can reuse its TypeSystemInfo when unifying.
        let candidates = default_candidates_for(&alpha, &preds_alpha, global_env);
        if candidates.is_empty() {
            continue;
        }

        let mut viable: Vec<(Ty, Subst)> = Vec::new();
        for (default_ty, from_constraint) in candidates {
            // Try α == default_ty without committing yet.
            let var_ty = Ty::Var(alpha.clone());
            let subst_try = match unify(&var_ty, &default_ty, &current_subst, &from_constraint.info)
            {
                Ok(s) => s,
                Err(_) => {
                    log.entries.push(DefaultingOutcome {
                        var: alpha.clone(),
                        default_ty: default_ty.clone(),
                        kind: DefaultingOutcomeKind::RejectedUnsat {
                            blocking_preds: preds_alpha.clone(),
                        },
                    });
                    continue;
                }
            };

            // Re-solve the cluster preds_alpha under this trial substitution.
            if let Ok(new_subst) =
                solve_predicates_for_class(&preds_alpha, global_env, &subst_try, ctx)
            {
                viable.push((default_ty.clone(), new_subst));
            } else {
                log.entries.push(DefaultingOutcome {
                    var: alpha.clone(),
                    default_ty: default_ty.clone(),
                    kind: DefaultingOutcomeKind::RejectedUnsat {
                        blocking_preds: preds_alpha.clone(),
                    },
                });
            }
        }

        // Multiple predicates can yield identical viable defaults (e.g. two
        // separate `Int[α]` constraints). De-duplicate by default type and
        // union their substitutions so we don't incorrectly treat identical
        // candidates as ambiguous.
        let mut deduped: BTreeMap<String, (Ty, Subst)> = BTreeMap::new();
        for (default_ty, subst_for_ty) in viable {
            let key = default_ty.to_string();
            match deduped.get_mut(&key) {
                Some((_, existing_subst)) => existing_subst.union(subst_for_ty),
                None => {
                    deduped.insert(key, (default_ty, subst_for_ty));
                }
            }
        }
        let viable: Vec<(Ty, Subst)> = deduped.into_values().collect();

        match viable.len() {
            0 => {
                // No viable default; leave α undecided.
            }
            1 => {
                let (default_ty, new_subst) = viable.into_iter().next().unwrap();
                // Commit the candidate's substitution to the main substitution.
                current_subst.union(new_subst);
                log.entries.push(DefaultingOutcome {
                    var: alpha.clone(),
                    default_ty,
                    kind: DefaultingOutcomeKind::Succeeded,
                });
            }
            _ => {
                log::debug!("[apply_defaulting] multiple candidates:");
                for (ty, subst) in &viable {
                    log::debug!("[apply_defaulting]   ty = {}, subst = {}", ty, subst);
                }
                let candidates = viable.into_iter().map(|(ty, _)| ty).collect::<Vec<_>>();
                log.entries.push(DefaultingOutcome {
                    var: alpha.clone(),
                    default_ty: Ty::Any,
                    kind: DefaultingOutcomeKind::RejectedAmbiguous { candidates },
                });
            }
        }
    }

    // Apply the final substitution to the residual constraints so that
    // downstream consumers (generalization, error reporting) see the
    // simplified forms after any defaults have been chosen.
    let mut residuals_after = residuals;
    for c in &mut residuals_after {
        c.apply_subst(&current_subst);
    }

    DefaultingResult {
        subst: current_subst,
        residuals: residuals_after,
        log,
    }
}

/// Find defaultable type-variable classes α based on residual predicates and
/// trait defaults.
fn find_defaultable_classes(
    residuals: &[Constraint],
    global_env: &GlobalEnv,
    subst: &Subst,
) -> HashSet<TyVar> {
    let mut defaultable = HashSet::new();

    for constraint in residuals {
        if let ConstraintKind::Class(cp) = &constraint.kind {
            if cp.args.is_empty() {
                continue;
            }

            // Trait must have a default(T).
            let trait_ty = match global_env.get_trait(&cp.name) {
                Some(t) => t,
                None => continue,
            };
            if trait_ty.default_ty.is_none() {
                continue;
            }

            // Receiver must be a meta variable class.
            let mut recv = cp.args[0].clone();
            recv.apply_subst(subst);

            if let Ty::Var(var) = recv {
                if var.is_meta() {
                    defaultable.insert(var);
                }
            }
        }
    }

    defaultable
}

/// Group residual predicates by the type-variable classes they mention.
fn group_predicates_by_class(
    residuals: &[Constraint],
    defaultable: &HashSet<TyVar>,
) -> Vec<(TyVar, Vec<Constraint>)> {
    let mut map: HashMap<TyVar, Vec<Constraint>> = HashMap::new();

    for constraint in residuals {
        // Collect all type variables mentioned in this predicate.
        let mut vars_in_constraint = HashSet::new();
        match &constraint.kind {
            ConstraintKind::Class(cp) => {
                for arg in &cp.args {
                    let mut free = HashSet::new();
                    arg.free_ty_vars(&mut free);
                    vars_in_constraint.extend(free.into_iter());
                }
            }
            ConstraintKind::HasField(hp) => {
                let mut free = HashSet::new();
                hp.record_ty.free_ty_vars(&mut free);
                vars_in_constraint.extend(free.into_iter());
                let mut free = HashSet::new();
                hp.field_ty.free_ty_vars(&mut free);
                vars_in_constraint.extend(free.into_iter());
            }
            ConstraintKind::Recv(rp) => {
                let mut free = HashSet::new();
                rp.recv_ty.free_ty_vars(&mut free);
                vars_in_constraint.extend(free.into_iter());
                let mut free = HashSet::new();
                rp.expr_ty.free_ty_vars(&mut free);
                vars_in_constraint.extend(free.into_iter());
            }
            ConstraintKind::Eq(eq) => {
                let mut free = HashSet::new();
                eq.lhs.free_ty_vars(&mut free);
                vars_in_constraint.extend(free.into_iter());
                let mut free = HashSet::new();
                eq.rhs.free_ty_vars(&mut free);
                vars_in_constraint.extend(free.into_iter());
            }
            ConstraintKind::Instantiate(inst) => {
                let mut free = HashSet::new();
                inst.ty.free_ty_vars(&mut free);
                vars_in_constraint.extend(free.into_iter());
            }
        }

        // For each defaultable class α that appears, add this predicate to its cluster.
        for var in vars_in_constraint {
            if defaultable.contains(&var) {
                map.entry(var).or_default().push(constraint.clone());
            }
        }
    }

    map.into_iter().collect()
}

/// Collect candidate default types for a given type-variable class `alpha`
/// from predicates of the form `C[alpha, …]` whose trait `C` has
/// `default(T_default)`.
fn default_candidates_for(
    alpha: &TyVar,
    preds_alpha: &[Constraint],
    global_env: &GlobalEnv,
) -> Vec<(Ty, Constraint)> {
    let mut candidates = Vec::new();

    for constraint in preds_alpha {
        let cp = match &constraint.kind {
            ConstraintKind::Class(cp) => cp,
            _ => continue,
        };
        if cp.args.is_empty() {
            continue;
        }

        // Receiver must be this type-variable class.
        let recv = &cp.args[0];
        if let Ty::Var(v) = recv {
            if v != alpha {
                continue;
            }
        } else {
            continue;
        }

        // Trait must have a default(T).
        let trait_ty = match global_env.get_trait(&cp.name) {
            Some(t) => t,
            None => continue,
        };
        if let Some(t_default) = &trait_ty.default_ty {
            candidates.push((t_default.clone(), constraint.clone()));
        }
    }

    candidates
}

/// Check whether a type-variable class represented by `var` is still flexible
/// under the current substitution.
fn is_flexible(var: &TyVar, subst: &Subst) -> bool {
    if !var.is_meta() {
        return false;
    }

    match subst.get(var) {
        None => true,
        Some(Ty::Var(v)) => v.is_meta(),
        Some(_) => false,
    }
}

/// Approximate the `will_be_generalized` check from Section 3.4.
///
/// We return true when the type-variable class appears as a free meta
/// variable in the type of any binding in the current group whose RHS is a
/// syntactic value. This matches the intent that such classes should be
/// quantified rather than defaulted.
fn will_be_generalized(
    var: &TyVar,
    module: &ModuleInput,
    group: &BindingGroup,
    ctx: &SolverContext,
    subst: &Subst,
) -> bool {
    if !var.is_meta() {
        return false;
    }

    for binding_id in &group.bindings {
        let is_value = module
            .binding_root_expr(*binding_id)
            .map(|root| is_syntactic_value_expr(module, root))
            .unwrap_or(false);
        if !is_value {
            continue;
        }

        if let Some(scheme) = ctx.binding_schemes.get(binding_id) {
            let mut ty = scheme.ty.clone();
            ty.apply_subst(subst);
            let mut free = HashSet::new();
            ty.free_ty_vars(&mut free);
            if free.contains(var) {
                return true;
            }
        }
    }

    false
}

/// Approximate `is_syntactic_value` from Section 3.4 using the expression
/// kinds available in `ModuleInput`.
fn is_syntactic_value_expr(module: &ModuleInput, expr: NodeId) -> bool {
    match module.expr_kind(expr) {
        Some(ExprKind::Closure { .. }) | Some(ExprKind::Function { .. }) => true,

        Some(ExprKind::Some { expr: inner }) => is_syntactic_value_expr(module, *inner),

        _ => false,
    }
}

/// Try to solve the cluster of predicates for a single type-variable class
/// using a local goal-solver run.
fn solve_predicates_for_class(
    preds: &[Constraint],
    global_env: &GlobalEnv,
    subst: &Subst,
    ctx: &mut SolverContext,
) -> Result<Subst, ()> {
    let mut subst = subst.clone();
    let batch = solve_constraints(preds, &[], global_env, &mut subst, ctx);
    if batch.unsolved.is_empty() {
        Ok(subst)
    } else {
        Err(())
    }
}

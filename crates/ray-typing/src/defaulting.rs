// Defaulting pass for the type system.
// This runs late in the pipeline to fill in unconstrained metas, as
// described in docs/type-system.md (Section 8).
//
// IMPORTANT: defaulting must NOT introduce new type errors; it is only
// allowed to resolve otherwise unconstrained meta variables in a way that
// does not change which programs type-check. Ambiguity reporting is a
// separate concern handled in the error model (Section 9).

use std::collections::{BTreeMap, HashMap, HashSet};

use ray_shared::{
    def::DefId,
    node_id::NodeId,
    ty::{Ty, TyVar},
    utils::{join, map_join},
};

use crate::{
    TypeCheckInput,
    binding_groups::BindingGroup,
    constraints::{Constraint, ConstraintKind},
    context::{ExprKind, SolverContext},
    env::TypecheckEnv,
    goal_solver::solve_constraints,
    types::{Subst, Substitutable as _},
    unify::unify,
};

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
    module: &TypeCheckInput,
    ctx: &mut SolverContext,
    group: &BindingGroup<DefId>,
    env: &dyn TypecheckEnv,
    residuals: Vec<Constraint>,
    subst: &Subst,
) -> DefaultingResult {
    let mut log = DefaultingLog::default();
    let mut current_subst = subst.clone();

    // Find defaultable type-variable classes α that appear as
    // receivers in residual class predicates from traits with defaults.
    let defaultable_classes = find_defaultable_classes(&residuals, env, &current_subst);
    log::debug!(
        "[apply_defaulting] defaultable_classes = {{ {} }}",
        join(&defaultable_classes, ", ")
    );

    // Build clusters of mutually-dependent defaultable classes and
    // their predicates. This is the cluster-level analogue of "group by α"
    // from the single-variable algorithm.
    let clusters = collect_defaulting_clusters(&residuals, &defaultable_classes);
    if clusters.is_empty() {
        log::debug!(
            "[apply_defaulting] no defaultable predicates in residuals: residuals = [{}]",
            join(&residuals, ", ")
        );
    }

    for (cluster_vars, preds_cluster) in clusters {
        // Skip classes that are no longer flexible. If any member of the
        // cluster is rigid, the whole cluster is blocked.
        let mut blocked = false;
        for var in &cluster_vars {
            if !is_flexible(var, &current_subst) {
                log.entries.push(DefaultingOutcome {
                    var: var.clone(),
                    default_ty: Ty::Any,
                    kind: DefaultingOutcomeKind::RejectedRigid,
                });
                log::debug!(
                    "[apply_defaulting] skipping non flexible variable: alpha = {}",
                    var
                );
                blocked = true;
            }

            // Skip classes that will be generalized into schemes according to
            // the value restriction (Section 3.4). If any member will be
            // generalized, we do not default the cluster.
            if will_be_generalized(var, module, group, ctx, &current_subst) {
                log.entries.push(DefaultingOutcome {
                    var: var.clone(),
                    default_ty: Ty::Any,
                    kind: DefaultingOutcomeKind::RejectedPoly,
                });
                blocked = true;
            }
        }
        if blocked {
            continue;
        }

        // Collect candidate defaults from all predicates C[alpha, …]
        // whose trait C has default(T_default). We keep the originating
        // constraint so we can reuse its TypeSystemInfo when unifying.
        let mut candidates_by_var = Vec::new();
        for var in &cluster_vars {
            let candidates = default_candidates_for(var, &preds_cluster, env);
            if candidates.is_empty() {
                log::debug!(
                    "[apply_defaulting] no default candidates: alpha = {}, predicates = [{}]",
                    var,
                    join(&preds_cluster, ", ")
                );
                blocked = true;
                break;
            }
            candidates_by_var.push((var.clone(), candidates));
        }
        if blocked {
            continue;
        }

        // Evaluate candidates per variable, but only accept an assignment if
        // the whole cluster is satisfiable under the trial substitution.
        let (viable, blocking_preds) = collect_cluster_viable_defaults(
            &candidates_by_var,
            &preds_cluster,
            env,
            &current_subst,
            ctx,
        );

        // Multiple predicates can yield identical viable defaults (e.g. two
        // separate `Int[α]` constraints). De-duplicate by assignment and
        // union substitutions so identical candidates do not appear ambiguous.
        let mut deduped: BTreeMap<String, (Vec<(TyVar, Ty)>, Subst)> = BTreeMap::new();
        for (assignment, subst_for_assignment) in viable {
            let key = assignment
                .iter()
                .map(|(var, ty)| format!("{}={}", var, ty))
                .collect::<Vec<_>>()
                .join(",");
            match deduped.get_mut(&key) {
                Some((_, existing_subst)) => existing_subst.union(subst_for_assignment),
                None => {
                    deduped.insert(key, (assignment, subst_for_assignment));
                }
            }
        }
        let viable: Vec<(Vec<(TyVar, Ty)>, Subst)> = deduped.into_values().collect();

        match viable.len() {
            0 => {
                let blocking_preds = blocking_preds.unwrap_or_else(|| preds_cluster.clone());
                for var in cluster_vars {
                    log.entries.push(DefaultingOutcome {
                        var,
                        default_ty: Ty::Any,
                        kind: DefaultingOutcomeKind::RejectedUnsat {
                            blocking_preds: blocking_preds.clone(),
                        },
                    });
                }
            }
            1 => {
                let (assignment, new_subst) = viable.into_iter().next().unwrap();
                log::debug!(
                    "[apply_defaulting] found single assignment: {}, new_subst = {}",
                    map_join(&assignment, ", ", |(v, t)| format!("({}, {})", v, t)),
                    new_subst
                );
                current_subst.union(new_subst);
                for (var, default_ty) in assignment {
                    log.entries.push(DefaultingOutcome {
                        var,
                        default_ty,
                        kind: DefaultingOutcomeKind::Succeeded,
                    });
                }
            }
            _ => {
                let mut candidates: HashMap<TyVar, Vec<Ty>> = HashMap::new();
                for (assignment, _) in viable {
                    for (var, ty) in assignment {
                        candidates.entry(var).or_default().push(ty);
                    }
                }
                for var in cluster_vars {
                    let mut options = candidates.remove(&var).unwrap_or_default();
                    options.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
                    options.dedup_by(|a, b| a.to_string() == b.to_string());
                    log.entries.push(DefaultingOutcome {
                        var,
                        default_ty: Ty::Any,
                        kind: DefaultingOutcomeKind::RejectedAmbiguous {
                            candidates: options,
                        },
                    });
                }
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
    env: &dyn TypecheckEnv,
    subst: &Subst,
) -> HashSet<TyVar> {
    let mut defaultable = HashSet::new();

    for constraint in residuals {
        if let ConstraintKind::Class(cp) = &constraint.kind {
            if cp.args.is_empty() {
                continue;
            }

            // Trait must have a default(T).
            let trait_ty = match env.trait_def(&cp.path) {
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
fn collect_defaulting_clusters(
    residuals: &[Constraint],
    defaultable: &HashSet<TyVar>,
) -> Vec<(Vec<TyVar>, Vec<Constraint>)> {
    let mut adjacency: HashMap<TyVar, HashSet<TyVar>> = HashMap::new();

    for constraint in residuals {
        // Track which defaultable metas appear in each predicate.
        let vars = defaultable_vars_in_constraint(constraint, defaultable);
        if vars.is_empty() {
            continue;
        }

        // Build an undirected graph where metas that co-occur in a predicate
        // must be defaulted together, so they share an edge.
        for var in &vars {
            adjacency.entry(var.clone()).or_default();
        }
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                adjacency
                    .entry(vars[i].clone())
                    .or_default()
                    .insert(vars[j].clone());
                adjacency
                    .entry(vars[j].clone())
                    .or_default()
                    .insert(vars[i].clone());
            }
        }
    }

    let mut visited = HashSet::new();
    let mut clusters = Vec::new();

    for var in defaultable {
        if visited.contains(var) {
            continue;
        }

        // Discover a connected component of mutually-dependent metas.
        let mut stack = vec![var.clone()];
        visited.insert(var.clone());
        let mut component = Vec::new();

        while let Some(node) = stack.pop() {
            component.push(node.clone());
            if let Some(neighbors) = adjacency.get(&node) {
                for neighbor in neighbors {
                    if visited.insert(neighbor.clone()) {
                        stack.push(neighbor.clone());
                    }
                }
            }
        }

        // Collect every residual predicate that mentions any meta in this component.
        let component_set: HashSet<TyVar> = component.iter().cloned().collect();
        let mut preds = Vec::new();
        for constraint in residuals {
            let vars = defaultable_vars_in_constraint(constraint, defaultable);
            if vars.iter().any(|v| component_set.contains(v)) {
                preds.push(constraint.clone());
            }
        }

        clusters.push((component, preds));
    }

    clusters
}

fn defaultable_vars_in_constraint(
    constraint: &Constraint,
    defaultable: &HashSet<TyVar>,
) -> Vec<TyVar> {
    let mut vars_in_constraint = HashSet::new();
    constraint.free_ty_vars(&mut vars_in_constraint);
    vars_in_constraint
        .into_iter()
        .filter(|var| defaultable.contains(var))
        .collect()
}

/// Collect candidate default types for a given type-variable class `alpha`
/// from predicates of the form `C[alpha, …]` whose trait `C` has
/// `default(T_default)`.
fn default_candidates_for(
    alpha: &TyVar,
    preds_alpha: &[Constraint],
    env: &dyn TypecheckEnv,
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
        let trait_ty = match env.trait_def(&cp.path) {
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
    module: &TypeCheckInput,
    group: &BindingGroup<DefId>,
    ctx: &SolverContext,
    subst: &Subst,
) -> bool {
    if !var.is_meta() {
        return false;
    }

    for def_id in group.bindings.iter().copied() {
        let is_value = module
            .binding_root_expr(def_id)
            .map(|root| is_syntactic_value_expr(module, root))
            .unwrap_or(false);
        if !is_value {
            continue;
        }

        if let Some(scheme) = ctx.binding_schemes.get(&def_id.into()) {
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
fn is_syntactic_value_expr(module: &TypeCheckInput, expr: NodeId) -> bool {
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
    subst: &Subst,
    ctx: &mut SolverContext,
) -> Result<Subst, Vec<Constraint>> {
    let mut subst = subst.clone();
    let batch = solve_constraints(preds, &[], &mut subst, ctx);
    if batch.unsolved.is_empty() {
        Ok(subst)
    } else {
        Err(batch.unsolved)
    }
}

fn collect_cluster_viable_defaults(
    candidates_by_var: &[(TyVar, Vec<(Ty, Constraint)>)],
    preds_cluster: &[Constraint],
    env: &dyn TypecheckEnv,
    subst: &Subst,
    ctx: &mut SolverContext,
) -> (Vec<(Vec<(TyVar, Ty)>, Subst)>, Option<Vec<Constraint>>) {
    let mut viable = Vec::new();
    let mut first_blocking = None;
    let mut assignments = Vec::new();

    fn visit(
        idx: usize,
        candidates_by_var: &[(TyVar, Vec<(Ty, Constraint)>)],
        preds_cluster: &[Constraint],
        env: &dyn TypecheckEnv,
        ctx: &mut SolverContext,
        current_subst: &Subst,
        assignments: &mut Vec<(TyVar, Ty)>,
        viable: &mut Vec<(Vec<(TyVar, Ty)>, Subst)>,
        first_blocking: &mut Option<Vec<Constraint>>,
    ) {
        if idx == candidates_by_var.len() {
            // Only check satisfiability after assigning defaults for every
            // meta in the cluster.
            match solve_predicates_for_class(preds_cluster, current_subst, ctx) {
                Ok(new_subst) => {
                    viable.push((assignments.clone(), new_subst));
                }
                Err(blocking_preds) => {
                    if first_blocking.is_none() {
                        *first_blocking = Some(blocking_preds);
                    }
                }
            }
            return;
        }

        let (var, candidates) = &candidates_by_var[idx];
        for (default_ty, from_constraint) in candidates {
            let var_ty = Ty::Var(var.clone());
            let subst_try = match unify(&var_ty, default_ty, current_subst, &from_constraint.info) {
                Ok(s) => s,
                Err(_) => continue,
            };
            // Try this candidate for the current variable, then recurse.
            assignments.push((var.clone(), default_ty.clone()));
            visit(
                idx + 1,
                candidates_by_var,
                preds_cluster,
                env,
                ctx,
                &subst_try,
                assignments,
                viable,
                first_blocking,
            );
            assignments.pop();
        }
    }

    visit(
        0,
        candidates_by_var,
        preds_cluster,
        env,
        ctx,
        subst,
        &mut assignments,
        &mut viable,
        &mut first_blocking,
    );

    (viable, first_blocking)
}

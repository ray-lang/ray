// Goal solver: resolves class predicates, HasField, and Recv.
//
// This implements a basic given/wanted matching pass as a concrete step
// toward the full goal solver described in Section 5.2 of the spec:
// - Givens are treated as assumptions available in a node and all descendants.
// - Class predicates can be solved by unifying their arguments against givens
//   or impls from the instance environment.
// - HasField predicates are solved using the instance environment's struct
//   metadata.
// - Recv predicates are solved using a small, built-in auto-ref/deref search.
// - Remaining wanteds are propagated upward toward the binding-group root and
//   reported as residual/unsatisfied predicates.

use std::collections::HashSet;

use ray_shared::{pathlib::ItemPath, resolution::DefTarget, ty::Ty};

use crate::{
    constraint_tree::ConstraintNode,
    constraints::{
        CallKind, ClassPredicate, Constraint, ConstraintKind, Predicate, RecvKind,
        ResolveCallConstraint,
    },
    context::{ImplFailure, InstanceFailure, InstanceFailureStatus, SolverContext},
    env::TypecheckEnv,
    impl_match::{
        ImplHeadMatch, collect_discarded_trial_metas, collect_meta_roots, commit_trial_subst,
        instantiate_impl_predicates, match_impl_head,
    },
    info::TypeSystemInfo,
    types::{
        ImplKind, MethodResolutionInfo, ReceiverMode, Subst, Substitutable, TraitField, TraitTy,
        TyScheme,
    },
    unify::{match_ty, unify},
};

#[derive(Debug)]
enum SolveOutcome {
    Solved,
    SolvedWith(Vec<Constraint>),
    UnsolvedInstance(InstanceSolveResult),
    Unsolved,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum InstanceSolveStatus {
    Solved,
    NoMatchingImpl,
    HeadMatchFailed,
    Deferred,
}

#[derive(Debug)]
struct InstanceSolveResult {
    status: InstanceSolveStatus,
    failures: Vec<ImplFailure>,
}

fn solve_constraint(
    constraint: &Constraint,
    givens_with_subst: &[Constraint],
    subst: &mut Subst,
    ctx: &mut SolverContext,
) -> SolveOutcome {
    log::debug!("[solve_constraint] {}", constraint);
    // First try to solve this wanted using the available givens.
    if solve_with_givens(constraint, givens_with_subst, subst) {
        return SolveOutcome::Solved;
    }

    // Next, try to solve via instance resolution.
    let instance_result = solve_with_instances(constraint, givens_with_subst, subst, ctx);
    match instance_result.status {
        InstanceSolveStatus::Solved => {
            return SolveOutcome::Solved;
        }
        InstanceSolveStatus::NoMatchingImpl | InstanceSolveStatus::HeadMatchFailed => {
            return SolveOutcome::UnsolvedInstance(instance_result);
        }
        InstanceSolveStatus::Deferred => {}
    }

    // Then try HasField / Recv using the global metadata and auto-ref/deref.
    if let ConstraintKind::HasField(_) = &constraint.kind {
        if solve_has_field(constraint, subst, ctx) {
            return SolveOutcome::Solved;
        }
    }

    if let ConstraintKind::Recv(_) = &constraint.kind {
        if solve_recv(constraint, subst) {
            return SolveOutcome::Solved;
        }
    }

    if let ConstraintKind::ResolveCall(_) = &constraint.kind {
        return solve_resolve_call(constraint, givens_with_subst, subst, ctx);
    }

    // Finally, treat syntactic matches against givens as solved.
    if givens_with_subst.contains(constraint) {
        return SolveOutcome::Solved;
    }

    SolveOutcome::Unsolved
}

/// Result of the goal solver phase over a binding group's constraint tree.
pub struct GoalSolveResult {
    /// Residual constraints that could not be solved (e.g. for error reporting
    /// or to be attached to generalized schemes).
    pub residual: Vec<Constraint>,
}

impl GoalSolveResult {
    pub fn new() -> Self {
        GoalSolveResult {
            residual: Vec::new(),
        }
    }
}

/// Outcome of solving a batch of predicate constraints.
pub struct ConstraintSolveResult {
    pub unsolved: Vec<Constraint>,
    pub solved: Vec<Constraint>,
}

pub fn solve_goals(
    root: &mut ConstraintNode,
    subst: &mut Subst,
    ctx: &mut SolverContext,
) -> GoalSolveResult {
    let mut result = GoalSolveResult::new();

    // Ensure the tree reflects the latest substitution before we start
    // predicate solving.
    root.apply_subst(subst);

    // Solve predicates bottom-up, propagating unsolved wanteds upward.
    let residual = solve_node(root, &Vec::new(), subst, ctx);

    // Apply any new equalities discovered during goal solving to the tree as
    // well, so downstream consumers see fully simplified constraints.
    root.apply_subst(subst);

    // At the binding-group root, any remaining predicates are considered
    // unsatisfied. We store them as residuals and also surface them as
    // TypeErrors for now.
    result.residual = residual;
    result
}

/// Core predicate-solving loop shared by both the tree-based solver and the
/// flat `solve_constraints` entry point.
pub fn solve_constraints(
    wanteds: &[Constraint],
    givens: &[Constraint],
    subst: &mut Subst,
    ctx: &mut SolverContext,
) -> ConstraintSolveResult {
    let base_givens = expand_givens_with_super_traits(givens, ctx.env());
    // Run predicate solving to a local fixpoint as required by the
    // entailment rules (docs/type-system.md Section 7): newly discovered
    // equalities from solved predicates may enable additional wanteds
    // to be discharged in a later pass.
    let mut worklist: Vec<Constraint> = wanteds.to_vec();
    let mut unsolved: Vec<Constraint> = Vec::new();
    let mut solved: Vec<Constraint> = Vec::new();

    loop {
        let mut givens_with_subst = base_givens.clone();
        for given in &mut givens_with_subst {
            given.apply_subst(subst);
        }

        let mut progress = false;
        unsolved.clear();
        let mut new_goals: Vec<Constraint> = Vec::new();

        for c in &worklist {
            let mut constraint = c.clone();
            constraint.apply_subst(subst);
            // Equality constraints should have been handled by the term
            // solver; we ignore any stragglers here.
            if matches!(&constraint.kind, ConstraintKind::Eq(_)) {
                continue;
            }

            match solve_constraint(&constraint, &givens_with_subst, subst, ctx) {
                SolveOutcome::Solved => {
                    solved.push(constraint);
                    progress = true;
                }
                SolveOutcome::SolvedWith(mut emitted) => {
                    solved.push(constraint);
                    progress = true;
                    new_goals.append(&mut emitted);
                }
                SolveOutcome::UnsolvedInstance(instance_result) => {
                    let status = match instance_result.status {
                        InstanceSolveStatus::NoMatchingImpl => {
                            InstanceFailureStatus::NoMatchingImpl
                        }
                        InstanceSolveStatus::HeadMatchFailed => {
                            InstanceFailureStatus::HeadMatchFailed
                        }
                        InstanceSolveStatus::Deferred | InstanceSolveStatus::Solved => {
                            InstanceFailureStatus::Deferred
                        }
                    };
                    ctx.record_predicate_failure(
                        &constraint,
                        InstanceFailure {
                            status,
                            failures: instance_result.failures,
                        },
                    );
                    unsolved.push(constraint);
                }
                SolveOutcome::Unsolved => {
                    unsolved.push(constraint);
                }
            }
        }

        if !progress {
            // No predicates were solved in this pass; we have reached a
            // local fixpoint for this batch of wanteds.
            break;
        }

        if unsolved.is_empty() && new_goals.is_empty() {
            // All predicates were solved.
            break;
        }

        // Continue solving the remaining predicates, using any additional
        // information accumulated in `subst` during this pass.
        worklist.clear();
        worklist.extend(unsolved.drain(..));
        worklist.extend(new_goals.drain(..));
        if !worklist.is_empty() {
            log::debug!("[solve_constraints] continuing with worklist:");
            for c in worklist.iter() {
                log::debug!("  {}", c);
            }
        } else {
            log::debug!("[solve_constraints] worklist is empty");
        }
    }

    ConstraintSolveResult { unsolved, solved }
}

fn class_predicate_from_ty(ty: &Ty) -> Option<ClassPredicate> {
    match ty {
        Ty::Proj(path, args) => Some(ClassPredicate::new(path.clone(), args.clone())),
        Ty::Const(path) => Some(ClassPredicate::new(path.clone(), Vec::new())),
        _ => None,
    }
}

fn instantiate_super_trait_constraints(
    cp: &ClassPredicate,
    info: &TypeSystemInfo,
    env: &dyn TypecheckEnv,
) -> Vec<Constraint> {
    let trait_ty = match env.trait_def(&cp.path) {
        Some(t) => t,
        None => return Vec::new(),
    };

    let mut subst = Subst::new();
    if let Ty::Proj(_, def_args) = &trait_ty.ty {
        for (param, actual) in def_args.iter().zip(cp.args.iter()) {
            if let Ty::Var(var) = param {
                subst.insert(var.clone(), actual.clone());
            }
        }
    }

    let mut supers = Vec::new();
    for super_ty in &trait_ty.super_traits {
        let mut instantiated = super_ty.clone();
        instantiated.apply_subst(&subst);
        if let Some(super_class) = class_predicate_from_ty(&instantiated) {
            let mut sup_info = info.clone();
            sup_info.parent_predicate(&Predicate::Class(cp.clone()));
            supers.push(Constraint::from_predicate(
                Predicate::Class(super_class),
                sup_info,
            ));
        }
    }

    supers
}

fn expand_givens_with_super_traits(
    givens: &[Constraint],
    env: &dyn TypecheckEnv,
) -> Vec<Constraint> {
    let mut result = givens.to_vec();
    let mut idx = 0;
    while idx < result.len() {
        if let ConstraintKind::Class(cp) = &result[idx].kind {
            let supers = instantiate_super_trait_constraints(cp, &result[idx].info, env);
            for sup in supers {
                if !result.iter().any(|existing| existing.kind == sup.kind) {
                    result.push(sup);
                }
            }
        }
        idx += 1;
    }
    result
}

/// Solve predicates at a node and its descendants, returning the list of
/// wanteds that could not be discharged by givens in this subtree.
fn solve_node(
    node: &ConstraintNode,
    inherited_givens: &Vec<Constraint>,
    subst: &mut Subst,
    ctx: &mut SolverContext,
) -> Vec<Constraint> {
    // Combine givens from ancestors with givens at this node.
    let mut combined_givens = inherited_givens.clone();
    combined_givens.extend(node.givens.clone());

    // Solve this node's wanteds against the combined givens.
    let batch = solve_constraints(&node.wanteds, &combined_givens, subst, ctx);
    combined_givens.extend(batch.solved.iter().cloned());
    let mut propagated = batch.unsolved;

    // Recurse into children, letting them inherit the combined givens.
    for child in &node.children {
        let child_unsolved = solve_node(child, &combined_givens, subst, ctx);
        propagated.extend(child_unsolved);
    }

    propagated
}

/// Try to solve a single wanted constraint using the available givens.
///
/// This function is intentionally limited to `Class` predicates. All other
/// wanted kinds are ignored (return `false`), even if a "similar" given exists.
///
/// We discharge a wanted when there is a matching given under the current
/// substitution, using the *receiver* (argument 0) as the only anchor:
///
/// - The receiver must already be equal under `subst` (we do not unify it).
/// - The receiver must not be an unconstrained meta (otherwise we'd be
///   guessing which receiver the predicate is about).
/// - Once the receiver matches, we may unify the remaining arguments to
///   refine inference.
///
/// IMPORTANT: givens are assumptions, not rewrite rules. This function must
/// not generate new type information by unifying wanteds against givens,
/// because that can incorrectly bind fresh metas to skolems from the local
/// context (e.g. a `where Int['a]` given causing an unrelated integer literal
/// meta to become `'a`).
fn solve_with_givens(wanted: &Constraint, givens: &[Constraint], subst: &mut Subst) -> bool {
    let ConstraintKind::Class(wp) = &wanted.kind else {
        return false;
    };

    for g in givens {
        let ConstraintKind::Class(gp) = &g.kind else {
            continue;
        };

        if wp.path != gp.path || wp.args.len() != gp.args.len() {
            continue;
        }

        let mut wanted_args = wp.args.clone();
        wanted_args.apply_subst(subst);
        let mut given_args = gp.args.clone();
        given_args.apply_subst(subst);

        // Only use the receiver (arg0) as an anchor. If it's still an
        // unconstrained meta, we refuse to solve from givens to avoid
        // capturing unrelated metas (e.g. `Int['a]` forcing `Int[?t]`).
        let recv = &wanted_args[0];
        // `wanted_args` has already had `subst` applied, so any meta that still
        // appears as `Ty::Var` here is necessarily unbound.
        if matches!(recv, Ty::Var(v) if v.is_meta()) {
            continue;
        }

        if wanted_args[0] != given_args[0] {
            continue;
        }

        // Receiver matches; unify the remaining arguments.
        let saved = subst.clone();
        let mut ok = true;
        for (wa, ga) in wanted_args.iter().skip(1).zip(given_args.iter().skip(1)) {
            match unify(wa, ga, subst, &wanted.info) {
                Ok(new_subst) => subst.union(new_subst),
                Err(_) => {
                    ok = false;
                    break;
                }
            }
        }

        if ok {
            return true;
        }

        *subst = saved;
    }

    false
}

/// Try to solve a class predicate using the instance environment's impls.
///
/// This is a conservative instance search: we look for impls whose trait name
/// matches the class predicate's name and whose arity matches the predicate's
/// arguments, and then attempt to unify the receiver and type arguments.
///
/// Note: Section 7 (multi-parameter type classes) requires that we treat
/// ambiguous matches (multiple viable impls) as ambiguity rather than
/// silently picking one. The current implementation stops at the first
/// successful impl; detection and reporting of such ambiguities is still
/// future work.
fn solve_with_instances(
    wanted: &Constraint,
    givens: &[Constraint],
    subst: &mut Subst,
    ctx: &mut SolverContext,
) -> InstanceSolveResult {
    log::debug!("[solve_with_instances] wanted = {}", wanted);
    let wp = match &wanted.kind {
        ConstraintKind::Class(wp) => wp,
        _ => {
            return InstanceSolveResult {
                status: InstanceSolveStatus::Deferred,
                failures: Vec::new(),
            };
        }
    };

    if wp.args.is_empty() {
        // Class predicates should always have at least a receiver argument.
        return InstanceSolveResult {
            status: InstanceSolveStatus::Deferred,
            failures: Vec::new(),
        };
    }

    // Do not "guess" a concrete receiver type for an unconstrained meta.
    // The receiver (arg0) is the only safe anchor for instance selection: if
    // it is still an unbound meta under the current substitution, then
    // choosing an impl (e.g. `Int[int]` for `Int[?t]`) would be arbitrary and
    // can block valid solutions that would otherwise be determined by other
    // constraints (e.g. via `Div['a,'a,'a]` or `Eq['a,'a]` givens).
    // let mut recv_ty = wp.args[0].clone();
    // recv_ty.apply_subst(subst);
    // if matches!(recv_ty, Ty::Var(v) if v.is_meta()) {
    //     return InstanceSolveResult {
    //         solved: false,
    //         failed_predicates: Vec::new(),
    //         no_matching_impl: false,
    //         impl_head: None,
    //     };
    // }
    let mut wp_args = wp.args.clone();
    wp_args.apply_subst(subst);
    if wp_args
        .iter()
        .all(|ty| matches!(ty, Ty::Var(v) if v.is_meta()))
    {
        // Do not continue if there isn't a grounded type in the arguments
        log::debug!(
            "[solve_with_instances] no grounded type in the arguments: {}",
            wp
        );
        return InstanceSolveResult {
            status: InstanceSolveStatus::Deferred,
            failures: Vec::new(),
        };
    }

    let mut successful_impls = Vec::new();
    let mut failures: Vec<ImplFailure> = Vec::new();
    let mut saw_head_match = false;

    for impl_ty in ctx.env().impls_for_trait(&wp.path) {
        let Some(head) = match_impl_head(wp, &impl_ty, subst, ctx, &wanted.info) else {
            continue;
        };

        let ImplHeadMatch {
            base_ty_head,
            ty_args_head,
            mut trial_subst,
            schema_subst,
            trial_metas,
        } = head;

        saw_head_match = true;

        // Discharge the impl's predicates under the trial substitution.
        // An impl is only a viable candidate if its `where` predicates can be
        // satisfied (otherwise we incorrectly treat it as a competing match).
        if !impl_ty.predicates.is_empty() {
            // The impl's predicates are written in terms of the impl's schema
            // variables (e.g. `UnsignedInt['a]`). Those schema variables must
            // be instantiated to the same fresh metas as the impl head
            // (base_ty/ty_args) before we can attempt to solve them.
            let instantiated_preds =
                instantiate_impl_predicates(&impl_ty, &schema_subst, &trial_subst);

            let instantiated_constraints = instantiated_preds
                .into_iter()
                .map(|p| Constraint::from_predicate(p, wanted.info.clone()))
                .collect::<Vec<_>>();

            let batch = solve_constraints(&instantiated_constraints, givens, &mut trial_subst, ctx);
            if !batch.unsolved.is_empty() {
                let mut args = Vec::with_capacity(1 + ty_args_head.len());
                args.push(base_ty_head.clone());
                args.extend(ty_args_head.iter().cloned());
                failures.push(ImplFailure {
                    impl_head: ClassPredicate::new(wp.path.clone(), args),
                    unsatisfied: batch.unsolved,
                });
                ctx.reuse_metas(trial_metas);
                continue;
            }
        }

        successful_impls.push((impl_ty, trial_subst, trial_metas));
    }

    match successful_impls.len() {
        0 => InstanceSolveResult {
            status: if saw_head_match {
                InstanceSolveStatus::HeadMatchFailed
            } else {
                InstanceSolveStatus::NoMatchingImpl
            },
            failures,
        },
        1 => {
            let (impl_ty, trial_subst, trial_metas) = successful_impls.remove(0);

            // Reuse only discarded trial metas; kept trial metas effectively
            // become part of global inference state because they are reachable
            // from pre-existing metas or residual obligations.
            let meta_roots = collect_meta_roots(wp, givens, &impl_ty, &trial_subst);
            let discard_trial_metas =
                collect_discarded_trial_metas(&meta_roots, &trial_metas, &trial_subst);
            let commit_subst = commit_trial_subst(&meta_roots, &trial_subst, subst);
            ctx.reuse_metas(discard_trial_metas);

            log::debug!(
                "[solve_with_instances] found solution: wanted = {}, impl_ty = {:?}, commit_subst = {}",
                wanted,
                impl_ty,
                commit_subst
            );
            subst.union(commit_subst);
            InstanceSolveResult {
                status: InstanceSolveStatus::Solved,
                failures: Vec::new(),
            }
        }
        _ => {
            // Put all the metas back that we didn't use
            for (_, _, fresh_metas) in successful_impls {
                ctx.reuse_metas(fresh_metas);
            }
            InstanceSolveResult {
                status: InstanceSolveStatus::Deferred,
                failures,
            }
        }
    }
}

/// Try to solve a HasField predicate using the instance environment's struct
/// metadata.
///
/// This uses the nominal struct definitions to confirm that the record type
/// has the named field and unifies the wanted field type with the declared
/// field type. For now this ignores type parameters on the struct; it simply
/// uses the mono field type from the StructTy.
fn solve_has_field(wanted: &Constraint, subst: &mut Subst, ctx: &mut SolverContext) -> bool {
    let hp = match &wanted.kind {
        ConstraintKind::HasField(hp) => hp,
        _ => return false,
    };

    // Resolve the record type to a nominal struct name, if possible.
    // Auto-deref pointer types (Ty::Ref) to access fields on the underlying struct.
    let mut record_ty = hp.record_ty.clone();
    record_ty.apply_subst(subst);

    // If the record type is a pointer, auto-deref to get the underlying type.
    let record_ty = match &record_ty {
        Ty::Ref(inner) => (**inner).clone(),
        other => other.clone(),
    };

    let struct_path = match &record_ty {
        Ty::Const(p) | Ty::Proj(p, _) => p,
        _ => {
            return false;
        }
    };

    let struct_ty = match ctx.env().struct_def(struct_path) {
        Some(s) => s,
        None => {
            return false;
        }
    };

    // Look up the field in the struct definition.
    let field_scheme = match struct_ty.get_field(&hp.field_name) {
        Some((_, scheme)) => scheme,
        None => return false,
    };

    // Instantiate schema variables from the nominal struct metadata before
    // unifying. This prevents schema vars (e.g. `?s6`) from leaking into the
    // global substitution when solving a particular field access site.
    let mut free_vars = HashSet::new();
    struct_ty.ty.free_ty_vars(&mut free_vars);
    field_scheme.free_ty_vars(&mut free_vars);
    let schema_vars = free_vars
        .into_iter()
        .filter(|var| var.is_schema())
        .collect::<Vec<_>>();

    let mut schema_subst = Subst::new();
    for var in schema_vars {
        let meta = ctx.fresh_meta();
        schema_subst.insert(var, meta);
    }

    // Unify the use-site record type with the (instantiated) nominal struct
    // type so the struct type arguments flow into the field type.
    let mut instantiated_struct_ty = struct_ty.ty.ty.clone();
    instantiated_struct_ty.apply_subst(&schema_subst);
    instantiated_struct_ty.apply_subst(subst);

    match unify(&record_ty, &instantiated_struct_ty, subst, &wanted.info) {
        Ok(new_subst) => subst.union(new_subst),
        Err(_) => return false,
    };

    // Unify the wanted field type with the declared field type.
    let mut field_ty = hp.field_ty.clone();
    field_ty.apply_subst(subst);

    let mut instantiated_field_ty = field_scheme.ty.clone();
    instantiated_field_ty.apply_subst(&schema_subst);
    instantiated_field_ty.apply_subst(subst);

    match unify(&field_ty, &instantiated_field_ty, subst, &wanted.info) {
        Ok(new_subst) => {
            log::debug!(
                "[solve_has_field] record_ty = {}, field_ty = {}, field_scheme.ty = {}, subst = {}",
                record_ty,
                field_ty,
                instantiated_field_ty,
                new_subst
            );
            subst.union(new_subst);
            true
        }
        Err(_) => false,
    }
}

/// Try to solve a Recv predicate using built-in auto-ref/deref rules.
///
/// This uses a deterministic rule (matching the previous implementation):
/// strip at most one `*` from the receiver expression type and then re-apply
/// it when the receiver kind requires a pointer.
fn solve_recv(wanted: &Constraint, subst: &mut Subst) -> bool {
    let rp = match &wanted.kind {
        ConstraintKind::Recv(rp) => rp,
        _ => return false,
    };

    log::debug!("[solve_recv] {}", rp);

    let mut recv_ty = rp.recv_ty.clone();
    recv_ty.apply_subst(subst);

    let mut expr_ty = rp.expr_ty.clone();
    expr_ty.apply_subst(subst);

    log::debug!("[solve_recv] recv_ty = {}, expr_ty = {}", recv_ty, expr_ty);

    // If the expression type is still an unconstrained meta, we cannot safely
    // decide whether to auto-deref it; doing so would incorrectly force the
    // expression to become the pointee type (e.g. `?t` -> `T[...]` instead of
    // `*T[...]`), which breaks pointer-receiver method calls like
    // `self.reserve(...)`.
    if matches!(&expr_ty, Ty::Var(v) if v.is_meta()) {
        return false;
    }

    let base_ty = match &expr_ty {
        Ty::Ref(inner) => (**inner).clone(),
        _ => expr_ty,
    };

    log::debug!("[solve_recv] base_ty = {}", base_ty,);

    let target_ty = match rp.kind {
        RecvKind::Value => base_ty,
        RecvKind::Ref => Ty::Ref(Box::new(base_ty)),
    };

    log::debug!(
        "[solve_recv] unify: recv_ty = {}, target_ty = {}",
        recv_ty,
        target_ty
    );
    match unify(&recv_ty, &target_ty, subst, &wanted.info) {
        Ok(new_subst) => {
            log::debug!("[solve_recv] new_subst = {}", new_subst);
            subst.union(new_subst);
            true
        }
        Err(err) => {
            log::debug!("[solve_recv] failed = {}", err);
            false
        }
    }
}

fn solve_resolve_call(
    wanted: &Constraint,
    givens: &[Constraint],
    subst: &mut Subst,
    ctx: &mut SolverContext,
) -> SolveOutcome {
    let ConstraintKind::ResolveCall(call) = &wanted.kind else {
        return SolveOutcome::Unsolved;
    };

    log::debug!("[solve_resolve_call] {}", call);
    match &call.kind {
        CallKind::Scoped { receiver_subst } => {
            // Scoped calls resolve the method by name on the subject type.
            // Unlike Instance calls, the subject type is explicit (T in T::method).
            let mut subject_ty = call.subject_ty.clone();
            subject_ty.apply_subst(subst);
            let maybe_subject_fqn = subject_fqn(&subject_ty);

            log::debug!(
                "[solve_resolve_call] scoped subject_ty = {}, method_name = {}",
                subject_ty,
                call.method_name
            );

            let mut ctx_bundle = ResolveCallContext {
                call,
                wanted,
                givens,
                subst,
                ctx,
                subject_ty: &subject_ty,
                subject_fqn: maybe_subject_fqn.as_ref(),
                receiver_subst: receiver_subst.as_ref(),
            };

            if let Some((trial_subst, outcome)) =
                solve_scoped_call(StaticRequirement::Either, &mut ctx_bundle)
            {
                subst.union(trial_subst);
                outcome
            } else {
                SolveOutcome::Unsolved
            }
        }
        CallKind::Instance => {
            let mut subject_ty = call.subject_ty.clone();
            subject_ty.apply_subst(subst);

            log::debug!(
                "[solve_resolve_call] subject_ty = {}, method_name = {}",
                subject_ty,
                call.method_name
            );

            // Candidate inherent methods require a headed receiver type (we
            // currently bucket inherent impls by receiver FQN).
            let maybe_subject_fqn = subject_fqn(&subject_ty);
            log::debug!(
                "[solve_resolve_call] maybe_subject_fqn = {:?}",
                maybe_subject_fqn
            );
            let chosen = match choose_method(
                maybe_subject_fqn.as_ref(),
                &call.method_name,
                StaticRequirement::NonStatic,
                givens,
                ctx.env(),
            ) {
                Some(chosen) => chosen,
                None => return SolveOutcome::Unsolved,
            };

            // Solve transactionally: if we cannot fully discharge the call (including
            // its qualifiers), do not commit any unifications to the outer subst.
            let mut call_ctx = ResolveCallContext {
                call,
                wanted,
                givens,
                subst,
                ctx,
                subject_ty: &subject_ty,
                subject_fqn: maybe_subject_fqn.as_ref(),
                receiver_subst: None,
            };

            let mut trial_subst = subst.clone();
            let outcome = solve_with_chosen_method(&chosen, None, &mut call_ctx, &mut trial_subst);

            match outcome {
                SolveOutcome::Solved | SolveOutcome::SolvedWith(_) => {
                    subst.union(trial_subst);

                    // Build resolution info
                    let resolution = match &chosen {
                        ChosenMethod::Inherent(method) => MethodResolutionInfo {
                            trait_target: None,
                            impl_target: method.target.clone(),
                            poly_scheme: method.scheme.clone(),
                        },
                        ChosenMethod::Trait(method) => MethodResolutionInfo {
                            trait_target: method.field.target.clone(),
                            impl_target: method.impl_target.clone(),
                            poly_scheme: method.field.ty.clone(),
                        }
                    };

                    // Record the method resolution in the side-table
                    ctx.method_resolutions.insert(call.call_site, resolution);
                    outcome
                }
                _ => outcome,
            }
        }
    }
}

#[derive(Clone, Debug)]
struct InherentMethod {
    scheme: TyScheme,
    is_static: bool,
    recv_mode: ReceiverMode,
    recv_ty: Ty,
    target: Option<DefTarget>,
}

#[derive(Clone, Debug)]
struct TraitMethod {
    trait_ty: TraitTy,
    field: TraitField,
    /// The impl method target, if the receiver type is concrete and known.
    impl_target: Option<DefTarget>,
}

#[derive(Debug)]
enum ChosenMethod {
    Inherent(InherentMethod),
    Trait(TraitMethod),
}

#[allow(dead_code)]
#[derive(Clone, Copy)]
enum StaticRequirement {
    Static,
    NonStatic,
    Either,
}

fn subject_fqn(subject_ty: &Ty) -> Option<ItemPath> {
    let mut ty = subject_ty.clone();
    loop {
        match ty {
            Ty::Ref(inner) | Ty::RawPtr(inner) => {
                ty = (*inner).clone();
            }
            Ty::Const(p) => return Some(p),
            Ty::Proj(p, _) => return Some(p),
            Ty::Var(v) if v.is_meta() => return None,
            _ => return None,
        }
    }
}

fn find_unique_inherent_method(
    env: &dyn TypecheckEnv,
    recv_fqn: &ItemPath,
    method_name: &str,
    required_is_static: StaticRequirement,
) -> Option<InherentMethod> {
    let impls = env.inherent_impls(recv_fqn);
    log::debug!(
        "[find_unique_inherent_method] recv_fqn = {}, impls = {:?}",
        recv_fqn,
        impls
    );
    let mut matches: Vec<InherentMethod> = Vec::new();

    for impl_ty in impls {
        let recv_ty = match &impl_ty.kind {
            ImplKind::Inherent { recv_ty } => recv_ty.clone(),
            _ => continue,
        };
        for field in &impl_ty.fields {
            let Some(name) = field.path.item_name() else {
                continue;
            };
            if name != method_name {
                continue;
            }
            match required_is_static {
                StaticRequirement::Static if !field.is_static => continue,
                StaticRequirement::NonStatic if field.is_static => continue,
                _ => {}
            }
            let Some(scheme) = &field.scheme else {
                continue;
            };
            matches.push(InherentMethod {
                scheme: scheme.clone(),
                is_static: field.is_static,
                recv_mode: field.recv_mode,
                recv_ty: recv_ty.clone(),
                target: field.target.clone(),
            });
        }
    }

    if matches.len() == 1 {
        matches.pop()
    } else {
        None
    }
}

fn solve_scoped_call(
    required_is_static: StaticRequirement,
    ctx_bundle: &mut ResolveCallContext<'_, '_>,
) -> Option<(Subst, SolveOutcome)> {
    let Some(subject_fqn) = ctx_bundle.subject_fqn else {
        return None;
    };

    let chosen = choose_method(
        Some(subject_fqn),
        &ctx_bundle.call.method_name,
        required_is_static,
        ctx_bundle.givens,
        ctx_bundle.ctx.env(),
    )?;
    log::debug!(
        "[solve_scoped_call] chosen = {:?}, subject_ty = {}, recv_subst = {:?}",
        chosen,
        ctx_bundle.subject_ty,
        ctx_bundle.receiver_subst
    );

    let mut trial_subst = ctx_bundle.subst.clone();
    let (outcome, resolution_info) = match chosen {
        ChosenMethod::Inherent(method) => {
            let impl_subst = receiver_subst_from_recv_ty(&method.recv_ty, ctx_bundle.subject_ty)?;
            log::debug!(
                "[solve_scoped_call] inherent recv_ty = {}, impl_subst = {}",
                method.recv_ty,
                impl_subst
            );
            let mut combined = impl_subst;
            if let Some(receiver_subst) = ctx_bundle.receiver_subst {
                if !combined.merge_checked(receiver_subst) {
                    log::debug!(
                        "[solve_scoped_call] receiver_subst merge failed: {} vs {}",
                        combined,
                        receiver_subst
                    );
                    return None;
                }
            }
            let resolution = MethodResolutionInfo {
                trait_target: None,
                impl_target: method.target.clone(),
                poly_scheme: method.scheme.clone(),
            };
            let outcome = solve_with_chosen_method(
                &ChosenMethod::Inherent(method),
                Some(&combined),
                ctx_bundle,
                &mut trial_subst,
            );
            (outcome, resolution)
        }
        ChosenMethod::Trait(method) => {
            let trait_subst = receiver_subst_for_trait(&method.trait_ty, ctx_bundle.subject_ty)?;
            log::debug!(
                "[solve_scoped_call] trait recv_ty = {}, trait_subst = {}",
                method.trait_ty.ty,
                trait_subst
            );
            let mut combined = trait_subst;
            if let Some(receiver_subst) = ctx_bundle.receiver_subst {
                if !combined.merge_checked(receiver_subst) {
                    log::debug!(
                        "[solve_scoped_call] receiver_subst merge failed: {} vs {}",
                        combined,
                        receiver_subst
                    );
                    return None;
                }
            }
            let resolution = MethodResolutionInfo {
                trait_target: method.field.target.clone(),
                impl_target: method.impl_target.clone(),
                poly_scheme: method.field.ty.clone(),
            };
            let outcome = solve_with_chosen_method(
                &ChosenMethod::Trait(method),
                Some(&combined),
                ctx_bundle,
                &mut trial_subst,
            );
            (outcome, resolution)
        }
    };

    match outcome {
        SolveOutcome::Solved | SolveOutcome::SolvedWith(_) => {
            // Record the method resolution in the side-table
            ctx_bundle
                .ctx
                .method_resolutions
                .insert(ctx_bundle.call.call_site, resolution_info);
            Some((trial_subst, outcome))
        }
        _ => None,
    }
}

struct ResolveCallContext<'a, 'ctx> {
    call: &'a ResolveCallConstraint,
    wanted: &'a Constraint,
    givens: &'a [Constraint],
    subst: &'a Subst,
    ctx: &'a mut SolverContext<'ctx>,
    subject_ty: &'a Ty,
    subject_fqn: Option<&'a ItemPath>,
    receiver_subst: Option<&'a Subst>,
}

fn choose_method<'a>(
    subject_fqn: Option<&ItemPath>,
    method_name: &str,
    required_is_static: StaticRequirement,
    givens: &[Constraint],
    env: &'a dyn TypecheckEnv,
) -> Option<ChosenMethod> {
    let inherent = subject_fqn.and_then(|subject_fqn| {
        find_unique_inherent_method(env, subject_fqn, method_name, required_is_static)
    });

    let trait_method = subject_fqn
        .and_then(|subject_fqn| {
            find_unique_trait_method_for_recv(env, subject_fqn, method_name, required_is_static)
        })
        .or_else(|| {
            // Prefer trait methods that are in-scope via givens (including
            // expanded supertraits). This supports generic receiver method calls
            // like `key: 'k` under `where Hash['k]` without requiring a headed
            // subject type.
            find_unique_trait_method_from_givens(givens, env, method_name, required_is_static)
        })
        .or_else(|| find_unique_trait_method(env, method_name, required_is_static));

    match (inherent, trait_method) {
        (Some(inherent), None) => Some(ChosenMethod::Inherent(inherent)),
        (None, Some(trait_method)) => Some(ChosenMethod::Trait(trait_method)),
        _ => None,
    }
}

fn find_unique_trait_method<'a>(
    env: &'a dyn TypecheckEnv,
    method_name: &str,
    required_is_static: StaticRequirement,
) -> Option<TraitMethod> {
    let mut matches: Vec<TraitMethod> = Vec::new();
    for trait_ty in env.all_traits() {
        if let Some(field) = trait_ty.get_field(method_name) {
            match required_is_static {
                StaticRequirement::Static if !field.is_static => continue,
                StaticRequirement::NonStatic if field.is_static => continue,
                _ => {}
            }
            matches.push(TraitMethod {
                trait_ty: trait_ty.clone(),
                field: field.clone(),
                impl_target: None, // No concrete impl available in global search
            });
        }
    }
    if matches.len() == 1 {
        matches.pop()
    } else {
        None
    }
}

fn find_unique_trait_method_from_givens<'a>(
    givens: &[Constraint],
    env: &'a dyn TypecheckEnv,
    method_name: &str,
    required_is_static: StaticRequirement,
) -> Option<TraitMethod> {
    let mut seen_trait_names: HashSet<&str> = HashSet::new();
    let mut matches: Vec<TraitMethod> = Vec::new();

    for given in givens {
        let ConstraintKind::Class(cp) = &given.kind else {
            continue;
        };
        if !seen_trait_names.insert(cp.path.as_str()) {
            continue;
        }

        let Some(trait_ty) = env.trait_def(&cp.path) else {
            continue;
        };
        let Some(field) = trait_ty.get_field(method_name).cloned() else {
            continue;
        };
        match required_is_static {
            StaticRequirement::Static if !field.is_static => continue,
            StaticRequirement::NonStatic if field.is_static => continue,
            _ => {}
        }
        matches.push(TraitMethod {
            trait_ty,
            field,
            impl_target: None, // No concrete impl available from givens
        });
    }

    if matches.len() == 1 {
        matches.pop()
    } else {
        None
    }
}

fn find_unique_trait_method_for_recv<'a>(
    env: &'a dyn TypecheckEnv,
    recv_fqn: &ItemPath,
    method_name: &str,
    required_is_static: StaticRequirement,
) -> Option<TraitMethod> {
    let impls = env.impls_for_recv(recv_fqn);
    let mut seen_traits: HashSet<ItemPath> = HashSet::new();
    let mut matches: Vec<TraitMethod> = Vec::new();

    for impl_ty in impls {
        let ImplKind::Trait { trait_ty, .. } = &impl_ty.kind else {
            continue;
        };
        let trait_path = match trait_ty {
            Ty::Const(p) | Ty::Proj(p, _) => p,
            _ => continue,
        };
        if !seen_traits.insert(trait_path.clone()) {
            continue;
        }

        // Find the impl field and extract its target
        let impl_field = impl_ty
            .fields
            .iter()
            .find(|field| field.path.item_name() == Some(&method_name.to_string()));

        let Some(impl_field) = impl_field else {
            continue;
        };
        let impl_target = impl_field.target.clone();

        let Some(trait_ty) = env.trait_def(&trait_path) else {
            continue;
        };
        let Some(field) = trait_ty.get_field(method_name).cloned() else {
            continue;
        };
        match required_is_static {
            StaticRequirement::Static if !field.is_static => continue,
            StaticRequirement::NonStatic if field.is_static => continue,
            _ => {}
        }
        matches.push(TraitMethod {
            trait_ty,
            field,
            impl_target,
        });
    }

    if matches.len() == 1 {
        matches.pop()
    } else {
        None
    }
}

fn receiver_subst_from_recv_ty(recv_ty: &Ty, subject_ty: &Ty) -> Option<Subst> {
    let mut vars = HashSet::new();
    recv_ty.free_ty_vars(&mut vars);
    let mut subst = Subst::new();
    if match_ty(recv_ty, subject_ty, &vars, &mut subst) {
        Some(subst)
    } else {
        None
    }
}

fn receiver_subst_for_trait(trait_ty: &TraitTy, subject_ty: &Ty) -> Option<Subst> {
    let Some(recv_ty) = trait_ty.ty.type_argument_at(0) else {
        return Some(Subst::new());
    };
    receiver_subst_from_recv_ty(recv_ty, subject_ty)
}

fn solve_chosen_method_call(
    scheme: &TyScheme,
    receiver_subst: Option<&Subst>,
    is_static: bool,
    recv_mode: ReceiverMode,
    trait_method: Option<(&TraitTy, &TraitField)>,
    ctx_bundle: &mut ResolveCallContext<'_, '_>,
    subst: &mut Subst,
) -> SolveOutcome {
    // Instantiate the method scheme at this use site.
    let mut method_ty = scheme.ty.clone();
    let mut qualifiers = scheme.qualifiers.clone();

    if let Some(receiver_subst) = receiver_subst {
        method_ty.apply_subst(receiver_subst);
        for pred in &mut qualifiers {
            pred.apply_subst(receiver_subst);
        }
    }

    let mut method_subst = Subst::new();
    for v in &scheme.vars {
        method_subst.insert(v.clone(), ctx_bundle.ctx.fresh_meta());
    }
    method_ty.apply_subst(&method_subst);
    for pred in &mut qualifiers {
        pred.apply_subst(&method_subst);
    }

    method_ty.apply_subst(subst);

    if !is_static {
        let Ok((param_tys, _ret_ty)) = method_ty.try_borrow_fn() else {
            return SolveOutcome::Unsolved;
        };
        let recv_param_ty = param_tys
            .first()
            .cloned()
            .unwrap_or_else(|| ctx_bundle.ctx.fresh_meta());

        // Enforce receiver compatibility (auto-ref/deref) without emitting a
        // separate constraint into the outer worklist.
        let recv_kind = match recv_mode {
            ReceiverMode::Ptr => RecvKind::Ref,
            _ => RecvKind::Value,
        };
        let recv_ok = solve_recv(
            &Constraint::recv(
                recv_kind,
                recv_param_ty.clone(),
                ctx_bundle.call.subject_ty.clone(),
                ctx_bundle.wanted.info.clone(),
            ),
            subst,
        );
        if !recv_ok {
            return SolveOutcome::Unsolved;
        }
    }

    let mut expected_fn_ty = ctx_bundle.call.expected_fn_ty.clone();
    expected_fn_ty.apply_subst(subst);

    // Unify the method type against the expected call signature.
    log::debug!(
        "[solve_chosen_method_call] unify: method_ty = {}, expected_fn_ty = {}",
        method_ty,
        expected_fn_ty
    );
    match unify(&method_ty, &expected_fn_ty, subst, &ctx_bundle.wanted.info) {
        Ok(new_subst) => subst.union(new_subst),
        Err(_) => return SolveOutcome::Unsolved,
    }

    let mut emitted: Vec<Constraint> = Vec::new();

    // If this is a trait method call, also emit the trait class predicate that
    // must hold for this receiver.
    if let Some((trait_ty, _field)) = trait_method {
        let mut trait_args = match &trait_ty.ty {
            Ty::Proj(_, args) => args.clone(),
            Ty::Const(_) => Vec::new(),
            _ => Vec::new(),
        };
        for arg in &mut trait_args {
            arg.apply_subst(&method_subst);
            arg.apply_subst(subst);
        }

        emitted.push(Constraint::class(
            trait_ty.path.clone(),
            trait_args,
            ctx_bundle.wanted.info.clone(),
        ));
    }

    // Emit qualifiers as additional goals rather than requiring them to be
    // immediately solvable. This allows ResolveCall to commit signature
    // equalities while deferring trait obligations.
    for mut pred in qualifiers {
        pred.apply_subst(subst);
        emitted.push(Constraint::from_predicate(
            pred,
            ctx_bundle.wanted.info.clone(),
        ));
    }

    if emitted.is_empty() {
        SolveOutcome::Solved
    } else {
        SolveOutcome::SolvedWith(emitted)
    }
}

fn solve_with_chosen_method(
    chosen: &ChosenMethod,
    receiver_subst: Option<&Subst>,
    ctx_bundle: &mut ResolveCallContext<'_, '_>,
    trial_subst: &mut Subst,
) -> SolveOutcome {
    match chosen {
        ChosenMethod::Inherent(method) => solve_chosen_method_call(
            &method.scheme,
            receiver_subst,
            method.is_static,
            method.recv_mode,
            None,
            ctx_bundle,
            trial_subst,
        ),
        ChosenMethod::Trait(method) => solve_chosen_method_call(
            &method.field.ty,
            receiver_subst,
            method.field.is_static,
            method.field.recv_mode,
            Some((&method.trait_ty, &method.field)),
            ctx_bundle,
            trial_subst,
        ),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use ray_shared::{
        def::DefId,
        file_id::FileId,
        node_id::NodeId,
        pathlib::ItemPath,
        ty::{SchemaVarAllocator, Ty, TyVar},
    };

    use crate::{
        constraints::{
            ClassPredicate, Constraint, ConstraintKind, Predicate, RecvKind, ResolveCallConstraint,
        },
        context::SolverContext,
        goal_solver::InstanceSolveStatus,
        info::TypeSystemInfo,
        mocks::MockTypecheckEnv,
        types::{
            FieldKind, ImplKind, ImplTy, ReceiverMode, Subst, Substitutable as _, TraitField,
            TraitTy, TyScheme,
        },
    };

    use super::{solve_constraints, solve_recv, solve_with_givens, solve_with_instances};

    #[test]
    fn solve_with_instances_instantiates_schema_vars_and_does_not_leak_trial_metas() {
        // Mock env with one impl:
        // impl Add[rawptr['a], uint, rawptr['a]]
        let mut typecheck_env = MockTypecheckEnv::new();
        typecheck_env.add_impl(ImplTy {
            kind: ImplKind::Trait {
                base_ty: Ty::rawptr(Ty::var("?s0")),
                trait_ty: Ty::proj("Add", vec![Ty::var("?s0"), Ty::var("?s1"), Ty::var("?s2")]),
                ty_args: vec![Ty::uint(), Ty::rawptr(Ty::var("?s0"))],
            },
            predicates: vec![],
            fields: vec![],
        });

        let mut schema_allocator = SchemaVarAllocator::new();
        let mut ctx = SolverContext::new(&mut schema_allocator, &typecheck_env);
        let mut subst = Subst::new();

        // Old metas (these are allowed to remain in the final substitution)
        let t0 = ctx.fresh_meta().as_tyvar();
        let t1 = ctx.fresh_meta().as_tyvar();

        // Wanted: Add[rawptr[T], ?t0, ?t1]
        let wanted = Constraint::from_predicate(
            Predicate::Class(ClassPredicate::new(
                "Add",
                vec![
                    Ty::rawptr(Ty::con("T")),
                    Ty::Var(t0.clone()),
                    Ty::Var(t1.clone()),
                ],
            )),
            TypeSystemInfo::default(),
        );

        // No givens for this test
        let givens: Vec<Constraint> = vec![];

        // Act
        let result = solve_with_instances(&wanted, &givens, &mut subst, &mut ctx);

        // Assert
        assert_eq!(result.status, InstanceSolveStatus::Solved);

        // Should force ?t0 = uint, ?t1 = rawptr[T]
        let mut rhs0 = subst.get(&t0).unwrap().clone();
        rhs0.apply_subst(&subst);
        assert_eq!(rhs0, Ty::uint());

        let mut rhs1 = subst.get(&t1).unwrap().clone();
        rhs1.apply_subst(&subst);
        assert_eq!(rhs1, Ty::rawptr(Ty::con("T")));

        // And crucially: subst should not contain any bindings for trial metas or scheme metas.
        for (k, v) in subst.iter() {
            assert!(!k.is_schema());
            assert!(k == &t0 || k == &t1);
            let mut free = HashSet::new();
            v.free_ty_vars(&mut free);
            for var in free {
                assert!(!var.is_schema())
            }
        }
    }

    #[test]
    fn solve_with_instances_returns_false_on_ambiguous_uint_vs_int_impls() {
        let mut typecheck_env = MockTypecheckEnv::new();

        // impl Add[rawptr['a], uint, rawptr['a]]
        typecheck_env.add_impl(ImplTy {
            kind: ImplKind::Trait {
                base_ty: Ty::rawptr(Ty::var("?s0")),
                trait_ty: Ty::proj("Add", vec![Ty::var("?s0"), Ty::var("?s1"), Ty::var("?s2")]),
                ty_args: vec![Ty::uint(), Ty::rawptr(Ty::var("?s0"))],
            },
            predicates: vec![],
            fields: vec![],
        });

        // impl Add[rawptr['a], int, rawptr['a]]
        typecheck_env.add_impl(ImplTy {
            kind: ImplKind::Trait {
                base_ty: Ty::rawptr(Ty::var("?s0")),
                trait_ty: Ty::proj("Add", vec![Ty::var("?s0"), Ty::var("?s1"), Ty::var("?s2")]),
                ty_args: vec![Ty::int(), Ty::rawptr(Ty::var("?s0"))],
            },
            predicates: vec![],
            fields: vec![],
        });

        let mut schema_allocator = SchemaVarAllocator::new();
        let mut ctx = SolverContext::new(&mut schema_allocator, &typecheck_env);
        let mut subst = Subst::new();

        let t0 = ctx.fresh_meta().as_tyvar();
        let t1 = ctx.fresh_meta().as_tyvar();

        let wanted = Constraint::from_predicate(
            Predicate::Class(ClassPredicate::new(
                "Add",
                vec![
                    Ty::rawptr(Ty::con("T")),
                    Ty::Var(t0.clone()),
                    Ty::Var(t1.clone()),
                ],
            )),
            TypeSystemInfo::default(),
        );

        let givens: Vec<Constraint> = vec![];

        let result = solve_with_instances(&wanted, &givens, &mut subst, &mut ctx);
        assert_ne!(result.status, InstanceSolveStatus::Solved);

        // Ensure we did not commit any bindings on ambiguity.
        assert!(subst.get(&t0).is_none());
        assert!(subst.get(&t1).is_none());
    }

    #[test]
    fn solve_with_instances_does_not_guess_for_unbound_meta_receiver() {
        let mut typecheck_env = MockTypecheckEnv::new();

        // impl Int[int]
        typecheck_env.add_impl(ImplTy {
            kind: ImplKind::Trait {
                base_ty: Ty::int(),
                trait_ty: Ty::proj("Int", vec![Ty::int()]),
                ty_args: vec![],
            },
            predicates: vec![],
            fields: vec![],
        });

        let mut schema_allocator = SchemaVarAllocator::new();
        let mut ctx = SolverContext::new(&mut schema_allocator, &typecheck_env);
        let mut subst = Subst::new();

        let t0 = ctx.fresh_meta().as_tyvar();
        let wanted = Constraint::from_predicate(
            Predicate::Class(ClassPredicate::new("Int", vec![Ty::Var(t0.clone())])),
            TypeSystemInfo::default(),
        );

        let givens: Vec<Constraint> = vec![];

        let result = solve_with_instances(&wanted, &givens, &mut subst, &mut ctx);
        assert_ne!(result.status, InstanceSolveStatus::Solved);
        assert!(subst.get(&t0).is_none());
    }

    #[test]
    fn solve_recv_ref_autorefs_once() {
        let mut subst = Subst::new();
        let wanted = Constraint::recv(
            RecvKind::Ref,
            Ty::ref_of(Ty::list(Ty::var("?t0"))),
            Ty::list(Ty::con("u32")),
            TypeSystemInfo::default(),
        );

        assert!(solve_recv(&wanted, &mut subst));
        assert_eq!(subst.get(&TyVar::new("?t0")), Some(&Ty::con("u32")));
    }

    #[test]
    fn solve_recv_value_autoderefs_once() {
        let mut subst = Subst::new();
        let wanted = Constraint::recv(
            RecvKind::Value,
            Ty::list(Ty::var("?t0")),
            Ty::ref_of(Ty::list(Ty::con("u32"))),
            TypeSystemInfo::default(),
        );

        assert!(solve_recv(&wanted, &mut subst));
        assert_eq!(subst.get(&TyVar::new("?t0")), Some(&Ty::con("u32")));
    }

    #[test]
    fn solve_with_givens_unifies_non_receiver_args_when_receiver_matches() {
        let mut subst = Subst::new();

        let k0 = TyVar::new("?k0");
        let t0 = TyVar::new("?t0");
        let wanted = Constraint::from_predicate(
            Predicate::Class(ClassPredicate::new(
                "Div",
                vec![
                    Ty::Var(k0.clone()),
                    Ty::Var(t0.clone()),
                    Ty::Var(k0.clone()),
                ],
            )),
            TypeSystemInfo::default(),
        );

        let given = Constraint::from_predicate(
            Predicate::Class(ClassPredicate::new(
                "Div",
                vec![
                    Ty::Var(k0.clone()),
                    Ty::Var(k0.clone()),
                    Ty::Var(k0.clone()),
                ],
            )),
            TypeSystemInfo::default(),
        );

        assert!(solve_with_givens(&wanted, &[given], &mut subst));
        assert_eq!(subst.get(&t0), Some(&Ty::Var(k0)));
    }

    #[test]
    fn solve_with_givens_does_not_guess_receiver_for_unconstrained_meta() {
        let mut subst = Subst::new();

        let k0 = TyVar::new("?k0");
        let t0 = TyVar::new("?t0");
        let wanted = Constraint::from_predicate(
            Predicate::Class(ClassPredicate::new("Int", vec![Ty::Var(t0.clone())])),
            TypeSystemInfo::default(),
        );

        let given = Constraint::from_predicate(
            Predicate::Class(ClassPredicate::new("Int", vec![Ty::Var(k0)])),
            TypeSystemInfo::default(),
        );

        assert!(!solve_with_givens(&wanted, &[given], &mut subst));
        assert!(subst.get(&t0).is_none());
    }

    #[test]
    fn resolve_call_instance_can_use_given_trait_method_with_schema_receiver() {
        let mut typecheck_env = MockTypecheckEnv::new();

        let a = TyVar::from("?s0");
        typecheck_env.add_trait(
            ItemPath::from("Hash"),
            TraitTy {
                path: ItemPath::from("Hash"),
                ty: Ty::Proj(ItemPath::from("Hash"), vec![Ty::Var(a.clone())]),
                super_traits: vec![],
                fields: vec![TraitField {
                    name: "hash".to_string(),
                    ty: TyScheme {
                        vars: vec![a.clone()],
                        qualifiers: vec![],
                        ty: Ty::Func(vec![Ty::Var(a.clone())], Box::new(Ty::u64())),
                    },
                    is_static: false,
                    recv_mode: ReceiverMode::Value,
                    kind: FieldKind::Method,
                    target: None,
                }],
                default_ty: None,
            },
        );

        let mut schema_allocator = SchemaVarAllocator::new();
        let mut ctx = SolverContext::new(&mut schema_allocator, &typecheck_env);
        let mut subst = Subst::new();

        let k = TyVar::from("?s1");
        let subject_ty = Ty::Var(k);
        let recv_param_ty = ctx.fresh_meta();
        let expected_fn_ty = Ty::Func(vec![recv_param_ty], Box::new(Ty::u64()));
        // Dummy NodeId for test
        let dummy_node_id = NodeId {
            owner: DefId {
                file: FileId(0),
                index: 0,
            },
            index: 0,
        };
        let wanted = Constraint {
            kind: ConstraintKind::ResolveCall(ResolveCallConstraint::new_instance(
                subject_ty.clone(),
                "hash",
                expected_fn_ty,
                dummy_node_id,
            )),
            info: TypeSystemInfo::default(),
        };

        let givens = vec![Constraint::class(
            "Hash",
            vec![subject_ty],
            TypeSystemInfo::default(),
        )];

        let res = solve_constraints(&[wanted], &givens, &mut subst, &mut ctx);
        assert!(res.unsolved.is_empty());
    }
}

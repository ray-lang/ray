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

use std::collections::{HashSet, VecDeque};

use ray_shared::utils::join;

use crate::{
    constraint_tree::ConstraintNode,
    constraints::{ClassPredicate, Constraint, ConstraintKind, Predicate},
    context::SolverContext,
    env::GlobalEnv,
    info::TypeSystemInfo,
    types::{Subst, Substitutable, Ty},
    unify::unify,
};

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
    global_env: &GlobalEnv,
    subst: &mut Subst,
    ctx: &mut SolverContext,
) -> GoalSolveResult {
    let mut result = GoalSolveResult::new();

    // Ensure the tree reflects the latest substitution before we start
    // predicate solving.
    root.apply_subst(subst);

    // Solve predicates bottom-up, propagating unsolved wanteds upward.
    let residual = solve_node(root, &Vec::new(), global_env, subst, ctx);

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
    global_env: &GlobalEnv,
    subst: &mut Subst,
    ctx: &mut SolverContext,
) -> ConstraintSolveResult {
    let base_givens = expand_givens_with_super_traits(givens, global_env);
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

        for c in &worklist {
            let mut constraint = c.clone();
            constraint.apply_subst(subst);
            // Equality constraints should have been handled by the term
            // solver; we ignore any stragglers here.
            if matches!(&constraint.kind, ConstraintKind::Eq(_)) {
                continue;
            }

            // First try to solve this wanted using the available givens.
            if solve_with_givens(&constraint, &givens_with_subst, subst) {
                solved.push(constraint);
                progress = true;
                continue;
            }

            // Next, try to solve via instance resolution.
            if solve_with_instances(&constraint, &givens_with_subst, global_env, subst, ctx) {
                solved.push(constraint);
                progress = true;
                continue;
            }

            // Then try HasField / Recv using the global metadata and
            // auto-ref/deref.
            if let ConstraintKind::HasField(_) = &constraint.kind {
                if solve_has_field(&constraint, global_env, subst) {
                    solved.push(constraint);
                    progress = true;
                    continue;
                }
            }

            if let ConstraintKind::Recv(_) = &constraint.kind {
                if solve_recv(&constraint, subst) {
                    solved.push(constraint);
                    progress = true;
                    continue;
                }
            }

            // Finally, treat syntactic matches against givens as solved.
            if givens_with_subst.contains(&constraint) {
                solved.push(constraint);
                progress = true;
                continue;
            }

            // Could not discharge this wanted in the current pass; keep it.
            unsolved.push(constraint);
        }

        if !progress {
            // No predicates were solved in this pass; we have reached a
            // local fixpoint for this batch of wanteds.
            break;
        }

        if unsolved.is_empty() {
            // All predicates were solved.
            break;
        }

        // Continue solving the remaining predicates, using any additional
        // information accumulated in `subst` during this pass.
        worklist.clear();
        worklist.extend(unsolved.drain(..));
    }

    ConstraintSolveResult { unsolved, solved }
}

fn class_predicate_from_ty(ty: &Ty) -> Option<ClassPredicate> {
    match ty {
        Ty::Proj(path, args) => Some(ClassPredicate::new(path.to_string(), args.clone())),
        Ty::Const(path) => Some(ClassPredicate::new(path.to_string(), Vec::new())),
        _ => None,
    }
}

fn instantiate_super_trait_constraints(
    cp: &ClassPredicate,
    info: &TypeSystemInfo,
    global_env: &GlobalEnv,
) -> Vec<Constraint> {
    let trait_ty = match global_env.get_trait(&cp.name) {
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
    global_env: &GlobalEnv,
) -> Vec<Constraint> {
    let mut result = givens.to_vec();
    let mut idx = 0;
    while idx < result.len() {
        if let ConstraintKind::Class(cp) = &result[idx].kind {
            let supers = instantiate_super_trait_constraints(cp, &result[idx].info, global_env);
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
    global_env: &GlobalEnv,
    subst: &mut Subst,
    ctx: &mut SolverContext,
) -> Vec<Constraint> {
    // Combine givens from ancestors with givens at this node.
    let mut combined_givens = inherited_givens.clone();
    combined_givens.extend(node.givens.clone());

    // Solve this node's wanteds against the combined givens.
    let batch = solve_constraints(&node.wanteds, &combined_givens, global_env, subst, ctx);
    combined_givens.extend(batch.solved.iter().cloned());
    let mut propagated = batch.unsolved;

    // Recurse into children, letting them inherit the combined givens.
    for child in &node.children {
        let child_unsolved = solve_node(child, &combined_givens, global_env, subst, ctx);
        propagated.extend(child_unsolved);
    }

    propagated
}

/// Try to solve a single wanted constraint using the available givens,
/// updating the shared substitution if successful.
///
/// This is a first concrete step toward the full goal solver: for now we only
/// support `Class` predicates by unifying their arguments against a matching
/// given with the same predicate name and arity.
fn solve_with_givens(wanted: &Constraint, givens: &[Constraint], subst: &mut Subst) -> bool {
    let ConstraintKind::Class(wp) = &wanted.kind else {
        return false;
    };

    for g in givens {
        let ConstraintKind::Class(gp) = &g.kind else {
            continue;
        };

        if wp.name == gp.name && wp.args.len() == gp.args.len() {
            // Attempt to unify each pair of arguments, updating
            // the shared substitution on success.
            let mut all_ok = true;
            let mut trial_subst = subst.clone();
            for (wa, ga) in wp.args.iter().zip(gp.args.iter()) {
                match unify(wa, ga, &trial_subst, &wanted.info) {
                    Ok(new_subst) => {
                        trial_subst.union(new_subst);
                    }
                    Err(_) => {
                        // ignore the error, since this doesn't match
                        all_ok = false;
                        break;
                    }
                }
            }

            if all_ok {
                subst.union(trial_subst);
                return true;
            }
        }
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
    global_env: &GlobalEnv,
    subst: &mut Subst,
    ctx: &mut SolverContext,
) -> bool {
    let wp = match &wanted.kind {
        ConstraintKind::Class(wp) => wp,
        _ => return false,
    };

    if wp.args.is_empty() {
        // Class predicates should always have at least a receiver argument.
        return false;
    }

    let recv_ty = &wp.args[0];
    let arg_tys = &wp.args[1..];

    let mut successful_impls = Vec::new();

    // Metas that existed before any probing begins. We use these as the
    // reachability roots to decide which trial metas must be kept.
    let mut meta_roots_set: HashSet<_> = HashSet::new();
    for ty in &wp.args {
        ty.free_ty_vars(&mut meta_roots_set);
    }
    for g in givens {
        g.free_ty_vars(&mut meta_roots_set);
    }
    let meta_roots: Vec<_> = meta_roots_set.into_iter().filter(|v| v.is_meta()).collect();

    for impl_ty in global_env.impls_for_trait(&wp.name) {
        if impl_ty.ty_args.len() != arg_tys.len() {
            continue;
        }

        // instantiate schema variables with fresh metas
        let mut vars = HashSet::new();
        impl_ty.free_ty_vars(&mut vars);
        let schema_vars = vars
            .iter()
            .filter(|var| var.is_schema())
            .cloned()
            .collect::<Vec<_>>();

        let mut schema_subst = Subst::new();
        let mut trial_metas = vec![];
        for var in schema_vars.iter() {
            let meta = ctx.fresh_meta();
            if let Ty::Var(v) = &meta {
                trial_metas.push(v.clone());
            }
            schema_subst.insert(var.clone(), meta);
        }

        let mut base_ty = impl_ty.base_ty.clone();
        let mut ty_args = impl_ty.ty_args.clone();
        base_ty.apply_subst(&schema_subst);
        ty_args.apply_subst(&schema_subst);

        // Start probe with a snapshot of the current global substitution.
        // The probe subst is allowed to be a superset/refinement of the global subst.
        let base_subst = subst.clone();
        let mut trial_subst = base_subst.clone();

        // Unify receiver type with the impl's base type.
        match unify(recv_ty, &base_ty, &trial_subst, &wanted.info) {
            Ok(new_subst) => {
                trial_subst.union(new_subst);
            }
            Err(_) => {
                ctx.reuse_metas(trial_metas);
                continue;
            }
        };

        // Unify the remaining arguments with the impl's type arguments.
        let mut ok = true;
        for (wanted_arg, impl_arg) in arg_tys.iter().zip(&ty_args) {
            match unify(wanted_arg, impl_arg, &trial_subst, &wanted.info) {
                Ok(new_subst) => {
                    trial_subst.union(new_subst);
                }
                Err(_) => {
                    ok = false;
                    break;
                }
            }
        }

        if !ok {
            ctx.reuse_metas(trial_metas);
            continue;
        }

        successful_impls.push((impl_ty, trial_subst, trial_metas));
    }

    match successful_impls.len() {
        0 => false,
        1 => {
            let (impl_ty, mut trial_subst, trial_metas) = successful_impls.remove(0);

            if !impl_ty.predicates.is_empty() {
                let mut instantiated = Vec::with_capacity(impl_ty.predicates.len());
                for pred in &impl_ty.predicates {
                    let mut p = pred.clone();
                    p.apply_subst(&trial_subst);
                    instantiated.push(Constraint::from_predicate(p, wanted.info.clone()));
                }

                let batch =
                    solve_constraints(&instantiated, givens, global_env, &mut trial_subst, ctx);
                if !batch.unsolved.is_empty() {
                    ctx.reuse_metas(trial_metas);
                    return false;
                }
            }

            // Check which trial metas are reachable from metas that existed
            // prior to the probe. Any reachable trial meta must be kept.
            let mut visited: HashSet<_> = HashSet::new();
            let mut work: Vec<_> = meta_roots.clone();

            // Also treat residuals as roots (future-proofing): if they mention
            // a trial meta, that meta must survive.
            for pred in &impl_ty.predicates {
                let mut p = pred.clone();
                p.apply_subst(&trial_subst);
                let mut vars = HashSet::new();
                p.free_ty_vars(&mut vars);
                work.extend(vars.into_iter().filter(|v| v.is_meta()));
            }

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

            let discard_trial_metas: Vec<_> = trial_metas
                .iter()
                .cloned()
                .filter(|m| !visited.contains(m))
                .collect();

            // Reuse only discarded trial metas; kept trial metas effectively
            // become part of global inference state because they are reachable
            // from pre-existing metas or residual obligations.
            ctx.reuse_metas(discard_trial_metas);

            // Commit only the delta for pre-existing metas.
            let mut commit_subst = Subst::new();
            for meta in &meta_roots {
                if let Some(rhs) = trial_subst.get(meta) {
                    let mut rhs_norm = rhs.clone();
                    rhs_norm.apply_subst(&trial_subst);

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

            subst.union(commit_subst);
            true
        }
        _ => {
            // Put all the metas back that we didn't use
            for (_, _, fresh_metas) in successful_impls {
                ctx.reuse_metas(fresh_metas);
            }
            false
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
fn solve_has_field(wanted: &Constraint, global_env: &GlobalEnv, subst: &mut Subst) -> bool {
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

    let struct_name = match &record_ty {
        Ty::Const(p) | Ty::Proj(p, _) => p.to_string(),
        _ => {
            return false;
        }
    };

    let struct_ty = match global_env.get_struct(&struct_name) {
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

    // Unify the wanted field type with the declared field type.
    let mut field_ty = hp.field_ty.clone();
    field_ty.apply_subst(subst);

    match unify(&field_ty, &field_scheme.ty, subst, &wanted.info) {
        Ok(new_subst) => {
            subst.union(new_subst);
            true
        }
        Err(_) => false,
    }
}

/// Try to solve a Recv predicate using built-in auto-ref/deref rules.
///
/// We conservatively explore a small space of receiver-adjustment steps from
/// the expression type (T, *T, rawptr[T], dereferenced forms) and attempt to
/// unify any of these candidate receiver types with the wanted receiver type.
fn solve_recv(wanted: &Constraint, subst: &mut Subst) -> bool {
    let rp = match &wanted.kind {
        ConstraintKind::Recv(rp) => rp,
        _ => return false,
    };

    let mut recv_ty = rp.recv_ty.clone();
    recv_ty.apply_subst(subst);

    let mut expr_ty = rp.expr_ty.clone();
    expr_ty.apply_subst(subst);

    // Breadth-first search over possible receiver adjustments, limited to a
    // small number of steps to avoid runaway exploration.
    let mut seen: HashSet<Ty> = HashSet::new();
    let mut queue: VecDeque<Ty> = VecDeque::new();

    seen.insert(expr_ty.clone());
    queue.push_back(expr_ty);

    let max_steps = 4usize;
    let mut steps = 0usize;

    while let Some(cur) = queue.pop_front() {
        if steps >= max_steps {
            break;
        }
        steps += 1;

        // Try to unify the current candidate receiver with the wanted receiver type
        match unify(&recv_ty, &cur, &subst, &wanted.info) {
            Ok(new_subst) => {
                subst.union(new_subst);
                return true;
            }
            Err(_) => {}
        }

        // Generate neighbors via simple auto-ref/deref rules.
        let ref_ty = Ty::Ref(Box::new(cur.clone()));
        if seen.insert(ref_ty.clone()) {
            queue.push_back(ref_ty);
        }

        match cur {
            Ty::Ref(inner) | Ty::RawPtr(inner) => {
                if seen.insert((*inner).clone()) {
                    queue.push_back(*inner);
                }
            }
            _ => {}
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, rc::Rc};

    use ray_shared::collections::namecontext::NameContext;

    use crate::{
        constraints::{ClassPredicate, Constraint, Predicate},
        context::SolverContext,
        env::GlobalEnv,
        info::TypeSystemInfo,
        types::{ImplTy, Subst, Substitutable as _, Ty},
    };

    use super::solve_with_instances;

    #[test]
    fn solve_with_instances_instantiates_schema_vars_and_does_not_leak_trial_metas() {
        let mut global_env = GlobalEnv::new();
        // Global env with one impl:
        // impl Add[rawptr['a], uint, rawptr['a]]
        global_env.add_impl(ImplTy {
            base_ty: Ty::rawptr(Ty::var("?s0")),
            trait_ty: Ty::proj("Add", vec![Ty::var("?s0"), Ty::var("?s1"), Ty::var("?s2")]),
            ty_args: vec![Ty::uint(), Ty::rawptr(Ty::var("?s0"))],
            predicates: vec![],
            fields: vec![],
        });

        let ncx = NameContext::new();
        let mut ctx = SolverContext::new(Rc::default(), &ncx, &global_env);
        let mut subst = Subst::new();

        // Old metas (these are allowed to remain in the final substitution)
        let t0 = ctx.fresh_meta().as_tyvar();
        let t1 = ctx.fresh_meta().as_tyvar();

        // Wanted: Add[rawptr[T], ?t0, ?t1]
        let wanted = Constraint::from_predicate(
            Predicate::Class(ClassPredicate::new(
                "Add".to_string(),
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
        let solved = solve_with_instances(&wanted, &givens, &global_env, &mut subst, &mut ctx);

        // Assert
        assert!(solved);

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
        let mut global_env = GlobalEnv::new();

        // impl Add[rawptr['a], uint, rawptr['a]]
        global_env.add_impl(ImplTy {
            base_ty: Ty::rawptr(Ty::var("?s0")),
            trait_ty: Ty::proj("Add", vec![Ty::var("?s0"), Ty::var("?s1"), Ty::var("?s2")]),
            ty_args: vec![Ty::uint(), Ty::rawptr(Ty::var("?s0"))],
            predicates: vec![],
            fields: vec![],
        });

        // impl Add[rawptr['a], int, rawptr['a]]
        global_env.add_impl(ImplTy {
            base_ty: Ty::rawptr(Ty::var("?s0")),
            trait_ty: Ty::proj("Add", vec![Ty::var("?s0"), Ty::var("?s1"), Ty::var("?s2")]),
            ty_args: vec![Ty::int(), Ty::rawptr(Ty::var("?s0"))],
            predicates: vec![],
            fields: vec![],
        });

        let ncx = NameContext::new();
        let mut ctx = SolverContext::new(Rc::default(), &ncx, &global_env);
        let mut subst = Subst::new();

        let t0 = ctx.fresh_meta().as_tyvar();
        let t1 = ctx.fresh_meta().as_tyvar();

        let wanted = Constraint::from_predicate(
            Predicate::Class(ClassPredicate::new(
                "Add".to_string(),
                vec![
                    Ty::rawptr(Ty::con("T")),
                    Ty::Var(t0.clone()),
                    Ty::Var(t1.clone()),
                ],
            )),
            TypeSystemInfo::default(),
        );

        let givens: Vec<Constraint> = vec![];

        let solved = solve_with_instances(&wanted, &givens, &global_env, &mut subst, &mut ctx);
        assert!(!solved);

        // Ensure we did not commit any bindings on ambiguity.
        assert!(subst.get(&t0).is_none());
        assert!(subst.get(&t1).is_none());
    }
}

// Constraint tree structures for the type system.
// This mirrors the constraint generation and tree construction described in
// docs/type-system.md Section 4 (especially 4.3 and 4.6).

use std::collections::HashSet;

use ray_shared::{
    def::DefId,
    local_binding::LocalBindingId,
    node_id::NodeId,
    ty::{Ty, TyVar},
    utils::{join, map_join},
};

use crate::{
    BindingKind, BindingRecord, PatternKind, TypeCheckInput,
    binding_groups::BindingGroup,
    constraints::{Constraint, ConstraintKind, ResolveCallConstraint},
    context::{AssignLhs, ExprKind, LhsPattern, Pattern, SolverContext},
    info::TypeSystemInfo,
    types::{Subst, Substitutable, TyScheme},
};

#[derive(Clone, Debug)]
pub struct SkolemizedAnnotation {
    ty: Ty,
    givens: Vec<Constraint>,
    skolems: Vec<TyVar>,
    subst: Subst,
}

fn skolemize_annotated_scheme(
    ctx: &mut SolverContext,
    def_id: DefId,
    scheme: &TyScheme,
    info: &TypeSystemInfo,
) -> SkolemizedAnnotation {
    if let Some(anno) = ctx.skolemized_schemes.get(&def_id.into()).cloned() {
        return anno;
    }

    let mut subst = Subst::new();
    let mut skolems = Vec::new();
    if !scheme.vars.is_empty() {
        for var in &scheme.vars {
            let skolem = ctx.fresh_skolem_var(def_id, var.clone(), info);
            let ty = Ty::Var(skolem.clone());
            subst.insert(var.clone(), ty.clone());
            skolems.push(skolem);
        }
    }

    let mut ty = scheme.ty.clone();
    ty.apply_subst(&subst);

    let mut givens = Vec::new();
    for predicate in &scheme.qualifiers {
        let mut pred = predicate.clone();
        pred.apply_subst(&subst);
        let mut pred_info = info.clone();
        pred_info.predicate_arising_from(&pred);
        ctx.record_required_predicate(def_id, pred.clone());
        givens.push(Constraint::from_predicate(pred, pred_info));
    }

    log::debug!("[skolemize_annotated_scheme] def_id = {:?}", def_id);
    log::debug!("[skolemize_annotated_scheme] scheme = {}", scheme);
    log::debug!("[skolemize_annotated_scheme] subst = {:?}", subst);
    log::debug!("[skolemize_annotated_scheme] skolemized_ty = {}", ty);
    log::debug!(
        "[skolemize_annotated_scheme] givens = [{}]",
        join(&givens, ", ")
    );
    log::debug!(
        "[skolemize_annotated_scheme] skolems = [{}]",
        join(&skolems, ", ")
    );

    let anno = SkolemizedAnnotation {
        ty,
        givens,
        skolems,
        subst,
    };

    ctx.skolemized_schemes.insert(def_id.into(), anno.clone());

    anno
}

/// Apply pattern-based constraints for guard positions (Pattern-if and
/// Pattern-while), following the "Pattern-if" and "Pattern-while" rules in
/// docs/type-system.md:
///
/// - For `some(x)` patterns, we constrain the scrutinee type to `nilable[T]`
///   for a fresh `T` and introduce `x : T` as a mono scheme in the context.
fn apply_pattern_guard(
    pattern: &Pattern,
    scrutinee: NodeId,
    ctx: &mut SolverContext,
    node: &mut ConstraintNode,
    info: &TypeSystemInfo,
) {
    let scrut_ty = ctx.expr_ty_or_fresh(scrutinee);
    apply_pattern_guard_with_ty(pattern, scrut_ty, ctx, node, info);
}

fn apply_pattern_guard_with_ty(
    pattern: &Pattern,
    scrut_ty: Ty,
    ctx: &mut SolverContext,
    node: &mut ConstraintNode,
    info: &TypeSystemInfo,
) {
    match pattern {
        Pattern::Some(local_id) => {
            let inner_ty = ctx.fresh_meta();
            let nilable_ty = Ty::nilable(inner_ty.clone());
            node.wanteds
                .push(Constraint::eq(scrut_ty, nilable_ty, info.clone()));

            ctx.binding_schemes
                .entry((*local_id).into())
                .or_insert_with(|| TyScheme::from_mono(inner_ty));
        }
        Pattern::Binding(local_id) => {
            // Simple binding pattern `x = e`: record a mono scheme x : Te.
            ctx.binding_schemes
                .entry((*local_id).into())
                .or_insert_with(|| TyScheme::from_mono(scrut_ty));
        }
        Pattern::Wild => {
            // `_` does not introduce bindings or additional constraints.
        }
    }
}

// Node identifier is intentionally opaque for now; in practice, this
// would be tied to AST nodes or binding-group-local scopes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ConstraintNodeId(pub u32);

#[derive(Clone, Debug)]
pub struct ConstraintNode {
    pub id: ConstraintNodeId,
    pub givens: Vec<Constraint>,
    pub wanteds: Vec<Constraint>,
    pub children: Vec<ConstraintNode>,
    pub metas: Vec<TyVar>,
    pub binding_nodes: Vec<BindingNode>,
}

impl ConstraintNode {
    pub fn new(id: ConstraintNodeId) -> Self {
        ConstraintNode {
            id,
            givens: vec![],
            wanteds: vec![],
            children: vec![],
            metas: vec![],
            binding_nodes: vec![],
        }
    }

    /// Walk this node's children and all descendants in a pre-order traversal,
    /// invoking the given callback on each node. This is a convenience helper for
    /// solver passes that need to inspect or transform the tree.
    pub fn walk_children(&self, f: &mut impl FnMut(&ConstraintNode)) {
        f(self);
        for child in &self.children {
            child.walk_children(f);
        }
    }

    /// Walk this node's children (mutably) and all descendants in a pre-order traversal,
    /// invoking the given callback on each node. This is a convenience helper for
    /// solver passes that need to inspect or transform the tree.
    pub fn walk_children_mut(&mut self, f: &mut impl FnMut(&mut ConstraintNode)) {
        f(self);
        for child in &mut self.children {
            child.walk_children_mut(f);
        }
    }

    /// Bottom-up fold over the constraint tree.
    ///
    /// This runs `f` on each node after computing results for all of its
    /// children, which matches the bottom-up solving order described in the
    /// type system spec.
    pub fn fold_post_order<T>(&self, f: &mut impl FnMut(&ConstraintNode, &[T]) -> T) -> T {
        let mut child_results = Vec::with_capacity(self.children.len());
        for child in &self.children {
            child_results.push(child.fold_post_order(f));
        }
        f(self, &child_results)
    }
}

/// Apply the pattern typing judgment Γ ⊢ p : T ⇝ (Δ, C) for an assignment
/// pattern on the left-hand side (docs/type-system.md A.7, A.8). This is
/// used to implement the general binding/destructuring assignment rule
/// for `lhs = rhs` when `lhs` is a pattern.
fn apply_lhs_pattern(
    input: &TypeCheckInput,
    ctx: &mut SolverContext,
    pat: &LhsPattern,
    expected_ty: Ty,
    pattern_id: NodeId,
    node: &mut ConstraintNode,
    info: &TypeSystemInfo,
) -> Vec<LocalBindingId> {
    let mut bindings = vec![];
    ctx.expr_types.insert(pattern_id, expected_ty.clone());
    match pat {
        LhsPattern::Binding(local_id) => {
            // Variable pattern `x`:
            //
            // - If this binding has been seen before in the current scope,
            //   we are in the simple variable assignment case and enforce
            //   `Te == T` (see "Simple variable assignment" in A.8).
            // - Otherwise, we treat this as a first-time binding and record
            //   `x : T` as a mono scheme; generalization decisions are made
            //   later at the binding-group boundary.
            let binding_ty = ctx.binding_ty_or_fresh(*local_id);
            log::debug!(
                "[apply_lhs_pattern] binding_ty (type of {:?}) = {}",
                local_id,
                binding_ty
            );
            node.wanteds
                .push(Constraint::eq(expected_ty, binding_ty, info.clone()));
            bindings.push(*local_id);
        }
        LhsPattern::Tuple(elems) => {
            // Tuple / sequence pattern `(p1, ..., pn)` or `p1, ..., pn`,
            // following the tuple pattern rule in A.7:
            //
            //   Γ ⊢ p1 : T1 ⇝ (Δ1, C1)   …   Γ ⊢ pn : Tn ⇝ (Δn, Cn)
            //   -----------------------------------------------------------------
            //   Γ ⊢ (p1, …, pn) : tuple[T1, …, Tn] ⇝ (Δ1 ∪ … ∪ Δn, C1 ∪ … ∪ Cn)
            //
            // We model this by:
            // - introducing fresh types T1..Tn,
            // - constraining expected_ty == tuple[T1..Tn],
            // - recursively applying the pattern judgment to each element.
            let mut elem_tys = Vec::with_capacity(elems.len());
            let record = input
                .pattern_records
                .get(&pattern_id)
                .expect("missing tuple pattern record");
            let child_ids = match &record.kind {
                PatternKind::Tuple { elems } => elems,
                _ => panic!("expected tuple pattern record"),
            };
            assert_eq!(child_ids.len(), elems.len(), "tuple pattern arity mismatch");

            for _ in elems {
                elem_tys.push(ctx.fresh_meta());
            }

            let tuple_ty = Ty::tuple(elem_tys.clone());
            node.wanteds
                .push(Constraint::eq(expected_ty, tuple_ty, info.clone()));

            for ((sub_pat, child_id), sub_ty) in
                elems.iter().zip(child_ids.iter()).zip(elem_tys.into_iter())
            {
                bindings.extend(apply_lhs_pattern(
                    input, ctx, sub_pat, sub_ty, *child_id, node, info,
                ));
            }
        }
        LhsPattern::Struct {
            struct_name: _,
            fields,
        } => {
            // Struct pattern `A { f1 = p1, ..., fn = pn }`, treated using
            // HasField predicates for each field (docs/type-system.md 4.5,
            // A.8). For each field `fi` we:
            //
            // - introduce a fresh type Tfi,
            // - constrain HasField[expected_ty, "fi", Tfi],
            // - recursively apply the pattern typing judgment to pi : Tfi.
            for (field_name, sub_pat) in fields {
                let field_ty = ctx.fresh_meta();
                node.wanteds.push(Constraint::has_field(
                    expected_ty.clone(),
                    field_name.clone(),
                    field_ty.clone(),
                    info.clone(),
                ));
                // TODO: record per-field pattern ids once struct patterns are lowered.
                bindings.extend(apply_lhs_pattern(
                    input, ctx, sub_pat, field_ty, pattern_id, node, info,
                ));
            }
        }
    }

    bindings
}

impl Substitutable for ConstraintNode {
    fn apply_subst(&mut self, subst: &Subst) {
        for g in &mut self.givens {
            g.apply_subst(subst);
        }
        for w in &mut self.wanteds {
            w.apply_subst(subst);
        }
        for child in &mut self.children {
            child.apply_subst(subst);
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum ConstraintTreeWalkItem<'a> {
    Wanted(&'a Constraint),
    Given(&'a Constraint),
    NodeStart(&'a ConstraintNode),
    NodeEnd(&'a ConstraintNode),
    BindingNodeStart(&'a BindingNode),
    BindingNodeEnd(&'a BindingNode),
}

impl std::fmt::Display for ConstraintTreeWalkItem<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintTreeWalkItem::Wanted(constraint) => write!(f, "Wanted({})", constraint),
            ConstraintTreeWalkItem::Given(constraint) => write!(f, "Given({})", constraint),
            ConstraintTreeWalkItem::NodeStart(node) => write!(f, "NodeStart({:?})", node.id),
            ConstraintTreeWalkItem::NodeEnd(node) => write!(f, "NodeEnd({:?})", node.id),
            ConstraintTreeWalkItem::BindingNodeStart(binding_node) => {
                write!(
                    f,
                    "BindingNode([{}])",
                    map_join(&binding_node.bindings, ", ", |b| format!("{:?}", b))
                )
            }
            ConstraintTreeWalkItem::BindingNodeEnd(binding_node) => {
                write!(
                    f,
                    "BindingNodeEnd([{}])",
                    map_join(&binding_node.bindings, ", ", |b| format!("{:?}", b))
                )
            }
        }
    }
}

pub(crate) fn walk_tree<'a, F>(node: &'a ConstraintNode, f: &mut F)
where
    F: FnMut(ConstraintTreeWalkItem<'a>),
{
    f(ConstraintTreeWalkItem::NodeStart(node));
    for c in node.wanteds.iter() {
        f(ConstraintTreeWalkItem::Wanted(c));
    }

    for c in node.givens.iter() {
        f(ConstraintTreeWalkItem::Given(c));
    }

    for child_node in node.children.iter() {
        walk_tree(child_node, f);
    }

    for node in node.binding_nodes.iter() {
        f(ConstraintTreeWalkItem::BindingNodeStart(node));
        walk_tree(&node.root, f);
        f(ConstraintTreeWalkItem::BindingNodeEnd(node));
    }
    f(ConstraintTreeWalkItem::NodeEnd(node));
}

/// Build the constraint tree for a single binding group.
///
/// This is the entry point for the "constraint generation" phase described in
/// the type system spec. In the full implementation this will walk the AST
/// for all bindings in the group (via `ModuleInput`), maintaining a stack of
/// active nodes and attaching equality and predicate constraints to the
/// appropriate nodes as it visits expressions and statements.
pub fn build_constraint_tree_for_group(
    input: &TypeCheckInput,
    ctx: &mut SolverContext,
    group: &BindingGroup<DefId>,
) -> ConstraintNode {
    // For now we create a single root node and delegate to a stubbed
    // constraint generator that will eventually walk the AST for all bindings
    // in this group.
    let mut root = ConstraintNode::new(ConstraintNodeId(0));
    generate_constraints_for_group(input, ctx, group, &mut root);
    root
}

/// Entry point for generating constraints for all bindings in a group.
///
/// - Iterate over each binding in the group.
/// - For each binding, create a child node that serves as the root for that
///   binding's constraint tree.
/// - Walk the binding's body, creating further child nodes for lexical scopes
///   (blocks, branches, etc.) and attaching equality and predicate
///   constraints to the appropriate nodes as described in Section 4.
pub fn generate_constraints_for_group(
    input: &TypeCheckInput,
    ctx: &mut SolverContext,
    group: &BindingGroup<DefId>,
    root: &mut ConstraintNode,
) {
    // This follows the spec's algorithm structurally: we create one child
    // node per binding, and then (recursively) one child node per nested
    // expression scope via `generate_constraints_for_expr`.
    let mut next_id = 1;
    for binding_id in &group.bindings {
        // The new lowering pipeline guarantees a binding record for every
        // binding that participates in type checking. If it is missing we
        // skip this binding rather than building an incomplete constraint
        // tree.
        let Some(record) = input.binding_records.get(binding_id) else {
            continue;
        };
        let Some(expr_root) = record.body_expr else {
            continue;
        };

        let binding_node_id = ConstraintNodeId(next_id);
        next_id += 1;
        let mut binding_node = ConstraintNode::new(binding_node_id);

        // Build info anchored at the binding's root expression.
        let mut binding_info = TypeSystemInfo::new();
        binding_info.source.extend(record.sources.clone());

        let BindingPreparation {
            binding_ty,
            ret_ty,
            givens,
            metas,
            skolem_subst,
        } = prepare_binding_context(ctx, *binding_id, record, &mut binding_info);
        binding_node.metas.extend(metas);
        binding_node.givens.extend(givens);

        if let Some(ret_ty) = &ret_ty {
            ctx.push_fn_ret(ret_ty.clone());
        }

        log::debug!(
            "[generate_constraints_for_group] binding prep: binding_ty = {}",
            binding_ty
        );
        generate_constraints_for_expr(
            input,
            ctx,
            *binding_id,
            skolem_subst.as_ref(),
            expr_root,
            &mut binding_node,
            &mut next_id,
        );

        // Ensure we have a type for the binding's root expression.
        let expr_ty = ctx.expr_ty_or_fresh(expr_root);

        // Relate the binding's type directly to the root expression's type.
        binding_node
            .wanteds
            .push(Constraint::eq(binding_ty, expr_ty, binding_info.clone()));

        if ret_ty.is_some() {
            ctx.pop_fn_ret();
        }

        root.children.push(binding_node);
    }
}

#[derive(Clone, Debug)]
pub struct BindingPreparation {
    pub binding_ty: Ty,
    pub ret_ty: Option<Ty>,
    pub givens: Vec<Constraint>,
    pub metas: Vec<TyVar>,
    pub skolem_subst: Option<Subst>,
}

/// Prepare the per-binding context prior to walking its body.
///
/// This mirrors the prose in docs/type-system.md Section 4.3:
/// - Introduce a mono type for the binding (synthesizing one if unannotated).
/// - For annotated bindings, skolemize the scheme and record the givens.
/// - For functions, seed parameter bindings and record the result type so
///   the caller can push it on the function-return stack.
pub fn prepare_binding_context(
    ctx: &mut SolverContext,
    def_id: DefId,
    record: &BindingRecord,
    binding_info: &mut TypeSystemInfo,
) -> BindingPreparation {
    // Following Section 4.3, introduce a mono type for the binding itself
    // and relate it to the type of its RHS expression via equality constraints
    // at the binding's root node. For annotated bindings we skolemize their
    // schemes and add the corresponding qualifiers as givens.
    let mut givens = vec![];
    let mut metas = vec![];
    let mut skolem_subst = None;
    let mut binding_ty = if let Some(scheme) = ctx.lookup_def_scheme(def_id) {
        if !scheme.vars.is_empty() || !scheme.qualifiers.is_empty() {
            let skolemized = skolemize_annotated_scheme(ctx, def_id, &scheme, binding_info);
            if !skolemized.skolems.is_empty() {
                binding_info.skolemized_type_scheme(&skolemized.skolems, &scheme);
            }
            givens.extend(skolemized.givens);
            metas.extend(skolemized.skolems);
            skolem_subst = Some(skolemized.subst.clone());
            skolemized.ty
        } else {
            scheme.ty
        }
    } else {
        ctx.binding_ty_or_fresh(def_id)
    };

    // Functions require special handling so that their parameter bindings
    // expose the correct types and the body can see the result meta.
    let ret_ty = match &record.kind {
        BindingKind::Function { params } => match &binding_ty {
            Ty::Func(param_tys, ret) => {
                // Annotated function: propagate the skolemized parameter
                // types down into each parameter binding so references to
                // the parameters pick up the right mono type.
                for (local_id, param_ty) in params.iter().zip(param_tys.iter()) {
                    ctx.binding_schemes
                        .insert((*local_id).into(), TyScheme::from_mono(param_ty.clone()));
                }
                Some((**ret).clone())
            }
            _ => {
                // Unannotated function: synthesize fresh metas for each
                // parameter and the result, then record the synthesized
                // function type so the body uses the same metas.
                let ret = ctx.fresh_meta();
                if let Ty::Var(v) = &ret {
                    metas.push(v.clone());
                }

                let synthesized: Vec<_> = params.iter().map(|_| ctx.fresh_meta()).collect();
                for ty in synthesized.iter() {
                    if let Ty::Var(v) = ty {
                        metas.push(v.clone());
                    }
                }

                binding_ty = Ty::func(synthesized.clone(), ret.clone());
                ctx.binding_schemes
                    .insert(def_id.into(), TyScheme::from_mono(binding_ty.clone()));
                Some(ret)
            }
        },
        _ => None,
    };

    BindingPreparation {
        binding_ty,
        ret_ty,
        givens,
        metas,
        skolem_subst,
    }
}

#[derive(Clone, Debug)]
pub struct BindingNode {
    pub bindings: Vec<LocalBindingId>,
    pub root: ConstraintNode,
}

/// Skeleton constraint generation for a single expression subtree.
///
/// In the full implementation this is where we:
/// - Attach equality constraints for expression typing rules (calls, literals,
///   conditionals, etc.).
/// - Attach predicate constraints for trait use, `HasField`, `Recv`, and so
///   on.
/// - Create additional child nodes for lexical scopes that introduce new
///   givens or environments.
fn generate_constraints_for_expr(
    input: &TypeCheckInput,
    ctx: &mut SolverContext,
    def_id: DefId,
    skolem_subst: Option<&Subst>,
    expr: NodeId,
    node: &mut ConstraintNode,
    next_id: &mut u32,
) {
    // Ensure this expression has a type in the context.
    let expr_ty = ctx.expr_ty_or_fresh(expr);

    // Seed TypeSystemInfo for this expression from its source span, if any.
    let mut info = TypeSystemInfo::new();
    if let Some(src) = input.expr_src(expr) {
        info.source.push(src.clone());
    }

    // Attach basic constraints based on the expression kind, following the
    // rules sketched in docs/type-system.md Section 4 (literals, calls,
    // if-expressions, pattern-if/while, nilable literals, and field
    // access/records per Section 4.5).
    if let Some(kind) = input.expr_kind(expr) {
        log::debug!(
            "[generate_constraints_for_expr] id = {:?}, kind = {:?}",
            expr,
            kind
        );
        match kind {
            ExprKind::LiteralInt => {
                // For unsuffixed integer literals, generate an `Int[T]`
                // class predicate (docs/type-system.md "Numeric literals"):
                //
                //   Γ ⊢ n ⇝ (?a, { Int[?a] })
                //
                // Defaulting and surrounding context will refine `?a`.
                log::debug!(
                    "[generate_constraints] literal int type (type of {}) = {}",
                    expr,
                    expr_ty
                );
                let trait_path = ctx.env().resolve_builtin("Int");
                node.wanteds
                    .push(Constraint::class(trait_path, vec![expr_ty], info));
            }
            ExprKind::LiteralIntSized(int_ty) => {
                // Sized integer literals (e.g. `1u32`) rely on surrounding
                // annotations (such as function result types) to fix their
                // type. We do not introduce an `Int` class predicate here;
                // the body type is related to the annotated result type via
                // the binding equality (see generate_constraints_for_group).
                node.wanteds
                    .push(Constraint::eq(expr_ty, int_ty.clone(), info));
            }
            ExprKind::LiteralFloat => {
                // For unsuffixed floating-point literals, generate a
                // `Float[T]` class predicate (see "Float literals").
                let trait_path = ctx.env().resolve_builtin("Float");
                node.wanteds
                    .push(Constraint::class(trait_path, vec![expr_ty], info));
            }
            ExprKind::LiteralFloatSized => {
                // Sized floating-point literals (e.g. `1.0f64`) rely on
                // surrounding annotations (such as function result types)
                // to fix their type. We do not introduce a `Float` class
                // predicate here; the body type is related to the annotated
                // result type via the binding equality.
            }
            ExprKind::LiteralBool(_) => {
                // Boolean literals have fixed type `bool` and no extra predicates
                // (see "Boolean literals").
                node.wanteds.push(Constraint::eq(expr_ty, Ty::bool(), info));
            }
            ExprKind::LiteralString => {
                // String literals have fixed type `string` (modeled here as
                // a primitive constant type).
                node.wanteds
                    .push(Constraint::eq(expr_ty, Ty::string(), info));
            }
            ExprKind::LiteralByteString => {
                // Byte-string literals have fixed type `bytes` (modeled as
                // a primitive constant type).
                node.wanteds
                    .push(Constraint::eq(expr_ty, Ty::bytes(), info));
            }
            ExprKind::LiteralByte => {
                // Byte literals have fixed type `byte`.
                node.wanteds.push(Constraint::eq(expr_ty, Ty::byte(), info));
            }
            ExprKind::LiteralChar => {
                // Char literals have fixed type `char`.
                node.wanteds.push(Constraint::eq(expr_ty, Ty::char(), info));
            }
            ExprKind::LiteralUnicodeEsc => {
                // Unicode escape sequence literals are treated as `string`
                // for typing purposes.
                node.wanteds
                    .push(Constraint::eq(expr_ty, Ty::string(), info));
            }
            ExprKind::Type { ty } => {
                // Meta-type expressions `T` have type `type[T]`.
                log::debug!("[generate_constraints_for_expr] type = {}", ty);
                node.wanteds
                    .push(Constraint::eq(expr_ty, Ty::ty_type(ty.clone()), info));
            }
            ExprKind::Missing => {
                // Missing expression placeholder: leave expr_ty unconstrained
                // so type checking can continue on the rest of the tree.
            }
            ExprKind::LocalRef(local_id) => {
                // Local binding references are handled by instantiating the
                // binding's scheme (Section 4.3) and equating it with the
                // reference expression's type.
                node.wanteds
                    .push(Constraint::inst_local(*local_id, expr_ty, info));
            }
            ExprKind::DefRef(def_id) => {
                // Top-level definition references are handled by instantiating
                // the definition's scheme and equating with the expression type.
                node.wanteds.push(Constraint::inst(*def_id, expr_ty, info));
            }
            ExprKind::ScopedAccess { def_id, lhs_ty, .. } => {
                // Scoped access `T::member`: `T[...]` instantiates the *type*
                // on the left-hand side, not the member binding itself.
                //
                // However, many associated members currently have schemes
                // whose qualifiers mention impl-scoped schema variables.
                //
                // Inside an annotated binding body, we already have a
                // schema->skolem substitution from skolemization. When the LHS
                // type is parameterized by those same schema vars, we can
                // derive the receiver substitution simply by restricting that
                // skolem substitution to the vars that appear in `lhs_ty`.
                let receiver_subst = skolem_subst.and_then(|skolem_subst| {
                    let mut lhs_vars = HashSet::new();
                    lhs_ty.free_ty_vars(&mut lhs_vars);

                    let mut subst = Subst::new();
                    for var in lhs_vars {
                        if let Some(ty) = skolem_subst.get(&var) {
                            subst.insert(var, ty.clone());
                        }
                    }

                    if subst.is_empty() { None } else { Some(subst) }
                });

                if let Some(receiver_subst) = receiver_subst {
                    node.wanteds.push(Constraint::inst_with_receiver_subst(
                        *def_id,
                        expr_ty,
                        receiver_subst,
                        info,
                    ));
                } else {
                    node.wanteds.push(Constraint::inst(*def_id, expr_ty, info));
                }
            }
            ExprKind::FieldAccess { recv, field } => {
                // Field access `e.field` generates a nominal HasField
                // predicate as described in Section 4.5:
                //
                //   HasField[Ty(e), "field", Ty(e.field)]
                //
                // The solver will use the struct declaration to relate this
                // to the declared field type.
                let recv_ty = ctx.expr_ty_or_fresh(*recv);

                node.wanteds
                    .push(Constraint::has_field(recv_ty, field.clone(), expr_ty, info));
            }
            ExprKind::StructLiteral { path, fields } => {
                // Struct construction `A { x: e1, ... }` is treated
                // nominally as in Section 4.5:
                //
                // - The overall expression has type `A`.
                // - For each field `f`, we generate a HasField predicate
                //   HasField[Ty(expr), "f", Ty(e_f)].
                //
                // The goal solver, using the nominal StructTy metadata,
                // relates these to the declared field types.
                let struct_ty = if let Some(struct_decl) = ctx.env().struct_def(path) {
                    let mut struct_scheme = struct_decl.ty.clone();
                    let mut subst = Subst::new();
                    for var in struct_scheme.vars.iter() {
                        subst.insert(var.clone(), ctx.fresh_meta());
                    }
                    struct_scheme.apply_subst(&subst);
                    struct_scheme.mono().clone()
                } else {
                    Ty::Const(path.clone())
                };

                // Tie the expression's type to the nominal struct type.
                node.wanteds.push(Constraint::eq(
                    expr_ty.clone(),
                    struct_ty.clone(),
                    info.clone(),
                ));

                for (field_name, field_expr) in fields {
                    let field_ty = ctx.expr_ty_or_fresh(*field_expr);

                    node.wanteds.push(Constraint::has_field(
                        expr_ty.clone(),
                        field_name.clone(),
                        field_ty,
                        info.clone(),
                    ));
                }
            }
            ExprKind::Closure { params, body } | ExprKind::Function { params, body } => {
                // Function expressions (closures), following the rule:
                //
                //   Γ, p1 : ?a1, …, pn : ?an ⊢ body ⇝ (Tbody, Cbody)
                //   -----------------------------------------------------------
                //   Γ ⊢ fn(p1, …, pn) { body } ⇝ ((?a1, …, ?an) -> Tbody, Cbody)
                //
                // Here we model the parameter types as fresh metas via the
                // binding schemes for each parameter binding, and we use the
                // body's expression type as the result type.
                let mut param_tys = Vec::with_capacity(params.len());
                for param in params {
                    param_tys.push(ctx.binding_ty_or_fresh(*param));
                }
                let body_ty = ctx.expr_ty_or_fresh(*body);
                let fn_ty = Ty::func(param_tys, body_ty.clone());

                node.wanteds
                    .push(Constraint::eq(expr_ty, fn_ty, info.clone()));

                ctx.push_fn_ret(body_ty.clone());

                let child_id = ConstraintNodeId(*next_id);
                *next_id += 1;
                let mut body_node = ConstraintNode::new(child_id);
                generate_constraints_for_expr(
                    input,
                    ctx,
                    def_id,
                    skolem_subst,
                    *body,
                    &mut body_node,
                    next_id,
                );
                node.children.push(body_node);

                // return here so we don't recurse children again
                ctx.pop_fn_ret();
                return;
            }
            ExprKind::List { items } => {
                // List literal `[e0, e1, ..., en]`. We treat this as
                // producing a mono `list[T]` type where `T` is the element
                // type of each item, and require that all items share the
                // same type.
                let elem_ty = ctx.fresh_meta();
                for item in items {
                    let item_ty = ctx.expr_ty_or_fresh(*item);
                    node.wanteds
                        .push(Constraint::eq(item_ty, elem_ty.clone(), info.clone()));
                }
                let list_path = ctx.env().resolve_builtin("list");
                let list_ty = Ty::proj(list_path, vec![elem_ty]);
                node.wanteds
                    .push(Constraint::eq(expr_ty, list_ty, info.clone()));
            }
            ExprKind::Dict { entries } => {
                // Dict literal `{ k0: v0, ..., kn: vn }` produces `dict[K, V]`
                // for fresh K and V, equates all keys/values, and requires
                // `Hash[K]` and `Eq[K, K]`.
                let key_ty = ctx.fresh_meta();
                let value_ty = ctx.fresh_meta();
                for (key, value) in entries {
                    let entry_key_ty = ctx.expr_ty_or_fresh(*key);
                    let entry_value_ty = ctx.expr_ty_or_fresh(*value);
                    node.wanteds
                        .push(Constraint::eq(entry_key_ty, key_ty.clone(), info.clone()));
                    node.wanteds.push(Constraint::eq(
                        entry_value_ty,
                        value_ty.clone(),
                        info.clone(),
                    ));
                }

                let dict_path = ctx.env().resolve_builtin("dict");
                let dict_ty = Ty::proj(dict_path, vec![key_ty.clone(), value_ty]);
                node.wanteds
                    .push(Constraint::eq(expr_ty, dict_ty, info.clone()));

                let hash_trait_fqn = ctx.env().resolve_builtin("Hash");
                node.wanteds.push(Constraint::class(
                    hash_trait_fqn,
                    vec![key_ty.clone()],
                    info.clone(),
                ));
                let eq_trait_fqn = ctx.env().resolve_builtin("Eq");
                node.wanteds.push(Constraint::class(
                    eq_trait_fqn,
                    vec![key_ty.clone(), key_ty],
                    info,
                ));
            }
            ExprKind::Set { items } => {
                // Set literal `{ e0, ..., en, }` produces `set[K]` for fresh K,
                // equates all elements, and requires `Hash[K]` and `Eq[K, K]`.
                let elem_ty = ctx.fresh_meta();
                for item in items {
                    let item_ty = ctx.expr_ty_or_fresh(*item);
                    node.wanteds
                        .push(Constraint::eq(item_ty, elem_ty.clone(), info.clone()));
                }

                let set_ty = Ty::proj(ctx.env().resolve_builtin("set"), vec![elem_ty.clone()]);
                node.wanteds
                    .push(Constraint::eq(expr_ty, set_ty, info.clone()));

                let hash_trait_fqn = ctx.env().resolve_builtin("Hash");
                node.wanteds.push(Constraint::class(
                    hash_trait_fqn,
                    vec![elem_ty.clone()],
                    info.clone(),
                ));
                let eq_trait_fqn = ctx.env().resolve_builtin("Eq");
                node.wanteds.push(Constraint::class(
                    eq_trait_fqn,
                    vec![elem_ty.clone(), elem_ty],
                    info,
                ));
            }
            ExprKind::Range {
                start,
                end,
                inclusive: _,
            } => {
                // Range expressions `start .. end` / `start ..= end` are
                // treated as producing a nominal `range[T]` struct where `T`
                // is the common element type of the endpoints (see the core
                // library definition in lib/core/range.ray).
                //
                // Γ ⊢ start ⇝ (Tstart, C1)
                // Γ ⊢ end   ⇝ (Tend,   C2)
                // fresh Tel
                // -------------------------------------------------
                // Γ ⊢ start .. end ⇝ (range[Tel],
                //   C1 ∪ C2 ∪ { Tel == Tstart, Tel == Tend })
                //
                let start_ty = ctx.expr_ty_or_fresh(*start);
                let end_ty = ctx.expr_ty_or_fresh(*end);
                let elem_ty = ctx.fresh_meta();

                // expr_ty == range[Tel]
                let range_fqn = ctx.env().resolve_builtin("range");
                let range_ty = Ty::proj(range_fqn, vec![elem_ty.clone()]);
                node.wanteds
                    .push(Constraint::eq(expr_ty.clone(), range_ty, info.clone()));

                // Tel == Tstart, Tel == Tend
                node.wanteds
                    .push(Constraint::eq(elem_ty.clone(), start_ty, info.clone()));
                node.wanteds.push(Constraint::eq(elem_ty, end_ty, info));
            }
            ExprKind::Deref { expr: inner } => {
                // Dereference (Section 1.1 "Pointer types"): if `e : *T`
                // then `*e : T`. We enforce this via the `Deref` trait:
                //
                //   Deref[Ty(e), Ty(*e)]
                //
                // This allows both `*T` and `rawptr[T]` to participate via
                // core library instances, without unifying the pointer
                // constructors.
                let inner_ty = ctx.expr_ty_or_fresh(*inner);
                let deref_trait_fqn = ctx.env().resolve_builtin("Deref");
                node.wanteds.push(Constraint::class(
                    deref_trait_fqn,
                    vec![inner_ty, expr_ty.clone()],
                    info.clone(),
                ));
            }
            ExprKind::Ref { expr: inner } => {
                // Explicit reference (Section 1.1 "Pointer types"):
                // if `e : T` then `ref e : *T`.
                let inner_ty = ctx.expr_ty_or_fresh(*inner);
                let ptr_ty = Ty::ref_of(inner_ty);
                node.wanteds
                    .push(Constraint::eq(expr_ty, ptr_ty, info.clone()));
            }
            ExprKind::Tuple { elems } => {
                // Tuple expression `(e0, e1, ..., en)` has type
                // `(T0, T1, ..., Tn)` where each Ti is the type of ei.
                let mut elem_tys = Vec::with_capacity(elems.len());
                for elem in elems {
                    elem_tys.push(ctx.expr_ty_or_fresh(*elem));
                }
                let tuple_ty = Ty::tuple(elem_tys);
                node.wanteds
                    .push(Constraint::eq(expr_ty, tuple_ty, info.clone()));
            }
            ExprKind::Index { container, index } => {
                // Indexing operation (Section A.3): `container[index]`.
                //
                // Γ ⊢ container ⇝ (Tc, Cc)
                // Γ ⊢ index ⇝ (Tidx, Ci)
                // ---------------------------------------
                // Γ ⊢ container[index] ⇝ (T, Cc ∪ Ci ∪ { Index[Tc, Tel, Tidx], T == nilable[Tel] })
                //
                // We generate the class predicate (matching `trait Index['a, 'el, 'idx]`):
                //   Index[Tc, Tel, Tidx]
                let container_ty = ctx.expr_ty_or_fresh(*container);
                let index_ty = ctx.expr_ty_or_fresh(*index);
                let elem_ty = ctx.fresh_meta();

                node.wanteds.push(Constraint::eq(
                    expr_ty.clone(),
                    Ty::nilable(elem_ty.clone()),
                    info.clone(),
                ));

                let index_fqn = ctx.env().resolve_builtin("Index");
                node.wanteds.push(Constraint::class(
                    index_fqn,
                    vec![container_ty, elem_ty, index_ty],
                    info.clone(),
                ));
            }
            ExprKind::BinaryOp {
                trait_fqn,
                method_fqn,
                lhs,
                rhs,
                ..
            } => {
                // Binary operators (docs/type-system.md "Operators"):
                //
                // Γ ⊢ e1 ⇝ (T1, C1)
                // Γ ⊢ e2 ⇝ (T2, C2)
                // fresh ?r
                // -------------------------------------------------
                // Γ ⊢ e1 op e2 ⇝ (?r, C1 ∪ C2 ∪ { OpTrait[T1, T2, ?r] })
                //
                // where `trait_name` is the operator's trait (e.g. "Add").
                let lhs_ty = ctx.expr_ty_or_fresh(*lhs);
                let rhs_ty = ctx.expr_ty_or_fresh(*rhs);
                // Base args: always lhs, rhs
                let mut args = vec![lhs_ty, rhs_ty];

                // Look up declared arity of the trait, if available.
                if let Some(trait_decl) = ctx.env().trait_def(trait_fqn) {
                    let arity = trait_decl.ty.arity();

                    // For operator traits we use the *last* type parameter as the result.
                    // Everything between [2 .. arity-1) gets fresh metas.
                    for i in 2..arity {
                        if i == arity - 1 {
                            args.push(expr_ty.clone());
                        } else {
                            args.push(ctx.fresh_meta());
                        }
                    }

                    let field_name = method_fqn.as_str();
                    if let Some(field) = trait_decl.get_field(field_name) {
                        if let Some((_, _, _, ret_ty)) = field.ty.try_borrow_fn() {
                            if !ret_ty.is_tyvar() {
                                node.wanteds.push(Constraint::eq(
                                    expr_ty,
                                    ret_ty.clone(),
                                    info.clone(),
                                ));
                            }
                        }
                    }
                } else {
                    // Fallback: assume 3-ary [lhs, rhs, result].
                    args.push(expr_ty);
                }
                node.wanteds
                    .push(Constraint::class(trait_fqn.clone(), args, info.clone()));
            }
            ExprKind::OpFunc { args, result, .. } => {
                let arg_tys: Vec<_> = args.iter().map(|id| ctx.expr_ty_or_fresh(*id)).collect();
                let result_ty = ctx.expr_ty_or_fresh(*result);
                let fn_ty = Ty::Func(arg_tys, Box::new(result_ty));
                node.wanteds
                    .push(Constraint::eq(expr_ty.clone(), fn_ty, info.clone()));
            }
            ExprKind::UnaryOp {
                trait_fqn,
                method_fqn,
                expr,
                ..
            } => {
                // Unary operators (docs/type-system.md "Operators"):
                //
                // Γ ⊢ e ⇝ (T, C)
                // fresh ?r
                // -------------------------------------------------
                // Γ ⊢ uop e ⇝ (?r, C ∪ { UnaryOpTrait[T, ?r] })
                //
                // where `trait_fqn` is the unary operator's trait (e.g. "core::Neg").
                let arg_ty = ctx.expr_ty_or_fresh(*expr);

                let mut args = vec![arg_ty];

                // Look up declared arity of the trait, if available.
                if let Some(trait_decl) = ctx.env().trait_def(trait_fqn) {
                    let arity = trait_decl.ty.arity();

                    // For operator traits we use the *last* type parameter as the result.
                    // Everything between [1 .. arity-1) gets fresh metas.
                    for i in 1..arity {
                        if i == arity - 1 {
                            args.push(expr_ty.clone());
                        } else {
                            args.push(ctx.fresh_meta());
                        }
                    }

                    let field_name = method_fqn.as_str();
                    if let Some(field) = trait_decl.get_field(field_name) {
                        if let Some((_, _, _, ret_ty)) = field.ty.try_borrow_fn() {
                            if !ret_ty.is_tyvar() {
                                node.wanteds.push(Constraint::eq(
                                    expr_ty,
                                    ret_ty.clone(),
                                    info.clone(),
                                ));
                            }
                        }
                    }
                } else {
                    // Fallback: assume 2-ary [arg, result].
                    args.push(expr_ty);
                }
                node.wanteds
                    .push(Constraint::class(trait_fqn.clone(), args, info.clone()));
            }
            ExprKind::Boxed { expr: inner } => {
                // Heap allocation / boxing (Section 1.1 "Pointer types"):
                // if `e : T` then `box e : *T`. We model this as a unary
                // constructor on types using the safe reference type.
                let inner_ty = ctx.expr_ty_or_fresh(*inner);
                let ptr_ty = Ty::ref_of(inner_ty);
                node.wanteds
                    .push(Constraint::eq(expr_ty, ptr_ty, info.clone()));
            }
            ExprKind::Some { expr: inner } => {
                // Nilable literal `some(e)` (Section "Nilable literals"):
                //
                // Γ ⊢ e ⇝ (T, C)
                // -------------------------------
                // Γ ⊢ some(e) ⇝ (nilable[T], C)
                //
                // Here we generate the equality tying expr_ty to nilable[T].
                let inner_ty = ctx.expr_ty_or_fresh(*inner);

                let nilable_ty = Ty::nilable(inner_ty);
                node.wanteds.push(Constraint::eq(expr_ty, nilable_ty, info));
            }
            ExprKind::Cast { expr: inner, ty } => {
                // Cast expressions `e as Tcast` (A.9).
                //
                // For now, we model casts as *type ascription* to the target
                // type, without requiring any relationship between the source
                // type `Te` and the target type `Tcast` (this matches the
                // previous v2 behavior, which treated cast as "change type").
                //
                // We still typecheck the operand and ensure the cast
                // expression's type equals the target type.
                let _inner_ty = ctx.expr_ty_or_fresh(*inner);
                let mut cast_ty = ty.clone();
                if let Some(anno) = ctx.skolemized_schemes.get(&def_id.into()) {
                    log::debug!(
                        "[generate_constraints] cast in def {:?}: raw cast_ty = {}",
                        def_id,
                        cast_ty
                    );
                    log::debug!(
                        "[generate_constraints] cast in def {:?}: skolem subst = {:?}",
                        def_id,
                        anno.subst
                    );
                    cast_ty.apply_subst(&anno.subst);
                    log::debug!(
                        "[generate_constraints] cast in def {:?}: cast_ty after subst = {}",
                        def_id,
                        cast_ty
                    );
                } else {
                    log::debug!(
                        "[generate_constraints] cast in def {:?}: missing skolemized scheme; cast_ty = {}",
                        def_id,
                        cast_ty
                    );
                }
                node.wanteds
                    .push(Constraint::eq(expr_ty, cast_ty, info.clone()));
            }
            ExprKind::New { count } => {
                // Heap allocation `new(T, count?)`, following:
                //
                //   Γ ⊢ count ⇝ (uint, C)
                //   ----------------------------
                //   Γ ⊢ new(T, count) ⇝ (*T, C)
                //
                //   ----------------------------
                //   Γ ⊢ new(T) ⇝ (*T, ∅)
                //
                // The target type `T` is provided by the parsed type
                // annotation and is attached to this expression by the
                // frontend; from the core type system's perspective we only
                // ensure that `count` has type `uint`. The result type `*T`
                // is reflected in `expr_ty` via that annotation.
                //
                // TODO: once type annotations are threaded into this IR,
                //       add an explicit equality tying `expr_ty` to `*T`
                //       (e.g. `Ty::ref_of(T)`) so the allocator result
                //       type participates directly in unification.
                if let Some(count_expr) = count {
                    let count_ty = ctx.expr_ty_or_fresh(*count_expr);
                    node.wanteds
                        .push(Constraint::eq(count_ty, Ty::uint(), info.clone()));
                }
            }
            ExprKind::Nil => {
                // Bare `nil` literal (Section "Nilable literals"):
                //
                // Γ ⊢ nil ⇝ (nilable[?a], ∅)
                //
                // We represent `nilable[?a]` as a nominal type constructor
                // applied to a fresh meta.
                let inner_ty = ctx.fresh_meta();
                let nilable_ty = Ty::nilable(inner_ty);
                node.wanteds.push(Constraint::eq(expr_ty, nilable_ty, info));
            }
            ExprKind::Assign {
                lhs_pattern,
                lhs,
                rhs,
            } => {
                // Assignment expressions (docs/type-system.md A.8).
                //
                // All assignment forms have type `unit`; they differ only in
                // how the left-hand side relates the right-hand side type to
                // existing or newly introduced bindings.
                //
                // We currently implement:
                // - Simple binding / re-assignment `x = e`.
                // - Deref assignment `*p = e` where `p` is a simple variable.
                // - Field assignment `recv.field = e` where `recv` is a simple
                //   variable.
                //
                // More complex mutation targets (indexing, nested fields) and
                // destructuring patterns are left for future work.
                let rhs_ty = ctx.expr_ty_or_fresh(*rhs);
                log::debug!(
                    "[generate_constraints] rhs_ty (type of {}) = {}",
                    rhs,
                    rhs_ty
                );

                // All assignments have result type `unit`.
                node.wanteds
                    .push(Constraint::eq(expr_ty, Ty::unit(), info.clone()));

                match lhs {
                    AssignLhs::Pattern(pat) => {
                        let rhs_node_id = ConstraintNodeId(*next_id);
                        *next_id += 1;
                        let mut rhs_node = ConstraintNode::new(rhs_node_id);

                        generate_constraints_for_expr(
                            input,
                            ctx,
                            def_id,
                            skolem_subst,
                            *rhs,
                            &mut rhs_node,
                            next_id,
                        );

                        let bindings = apply_lhs_pattern(
                            input,
                            ctx,
                            pat,
                            rhs_ty.clone(),
                            *lhs_pattern,
                            node,
                            &info,
                        );

                        node.binding_nodes.push(BindingNode {
                            bindings,
                            root: rhs_node,
                        });

                        // we return here so we don't recurse children, since we already did
                        return;
                    }
                    AssignLhs::Index { container, index } => {
                        // Index assignment `container[index] = rhs` (A.8):
                        //
                        //   Γ ⊢ container ⇝ (Tc, Cc)
                        //   Γ ⊢ index ⇝ (Tidx, Ci)
                        //   Γ ⊢ rhs ⇝ (Trhs, Crhs)
                        //   fresh Tel
                        //   --------------------------------------------------
                        //   Γ ⊢ container[index] = rhs ⇝ (unit,
                        //      Cc ∪ Ci ∪ Crhs ∪ { Index[Tc, Tel, Tidx], Trhs == Tel })
                        //
                        let container_ty = ctx.binding_ty_or_fresh(*container);
                        let index_ty = ctx.expr_ty_or_fresh(*index);
                        let elem_ty = ctx.fresh_meta();
                        ctx.expr_types.insert(*lhs_pattern, elem_ty.clone());

                        let index_fqn = ctx.env().resolve_builtin("Index");
                        node.wanteds.push(Constraint::class(
                            index_fqn,
                            vec![container_ty, elem_ty.clone(), index_ty],
                            info.clone(),
                        ));
                        node.wanteds
                            .push(Constraint::eq(rhs_ty, elem_ty, info.clone()));
                    }
                    AssignLhs::Deref(binding) => {
                        // Deref assignment `*p = e` (Section A.8):
                        //
                        // Γ ⊢ p ⇝ (Tp, Cp)
                        // Γ ⊢ e ⇝ (Te, Ce)
                        // fresh Tcell
                        // ------------------------------------------------
                        // Γ ⊢ *p = e ⇝ (unit,
                        //   Cp ∪ Ce ∪ { Deref[Tp, Tcell], Te == Tcell })
                        //
                        // We model dereference via the `Deref` trait rather
                        // than by unifying `Tp` with `*Tcell`, so both `*T`
                        // and `rawptr[T]` can be dereferenced when instances
                        // exist.
                        let ptr_ty = ctx.binding_ty_or_fresh(*binding);
                        let cell_ty = ctx.fresh_meta();
                        ctx.expr_types.insert(*lhs_pattern, cell_ty.clone());
                        node.wanteds.push(Constraint::class(
                            ctx.env().resolve_builtin("Deref"),
                            vec![ptr_ty, cell_ty.clone()],
                            info.clone(),
                        ));
                        // Te == Tcell
                        node.wanteds
                            .push(Constraint::eq(rhs_ty, cell_ty, info.clone()));
                    }
                    AssignLhs::Field { recv, field } => {
                        // Field assignment `recv.field = rhs` (Section A.8):
                        //
                        // Γ ⊢ recv ⇝ (Te, Ce)
                        // Γ ⊢ rhs ⇝ (Trhs, Crhs)
                        // fresh Tx
                        // ------------------------------------------------
                        // Γ ⊢ recv.field = rhs ⇝
                        //   (unit, Ce ∪ Crhs ∪ { HasField[Te, "field", Tx], Trhs == Tx })
                        //
                        let recv_ty = ctx.binding_ty_or_fresh(*recv);
                        let field_ty = ctx.fresh_meta();

                        ctx.expr_types.insert(*lhs_pattern, field_ty.clone());
                        node.wanteds.push(Constraint::has_field(
                            recv_ty,
                            field.clone(),
                            field_ty.clone(),
                            info.clone(),
                        ));
                        node.wanteds
                            .push(Constraint::eq(rhs_ty, field_ty, info.clone()));
                    }
                    AssignLhs::ErrorPlaceholder => {
                        ctx.expr_types.insert(*lhs_pattern, Ty::unit());
                    }
                }
            }
            ExprKind::Sequence { items } => {
                if let Some((last, _)) = items.split_last() {
                    let last_ty = ctx.expr_ty_or_fresh(*last);
                    node.wanteds
                        .push(Constraint::eq(expr_ty, last_ty, info.clone()));
                } else {
                    node.wanteds
                        .push(Constraint::eq(expr_ty, Ty::unit(), info.clone()));
                }
            }
            ExprKind::Wrapper { expr: inner } => {
                let inner_ty = ctx.expr_ty_or_fresh(*inner);
                node.wanteds
                    .push(Constraint::eq(expr_ty, inner_ty, info.clone()));
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                // If expression typing rule (Section 4, "If expressions"):
                //
                // Γ ⊢ cond ⇝ (Tcond, Ccond)
                // Γ ⊢ e_then ⇝ (T_then, C_then)
                // Γ ⊢ e_else ⇝ (T_else, C_else)
                // -------------------------------------------------------------
                // Γ ⊢ if cond { e_then } else { e_else } ⇝
                //   (T, Ccond ∪ C_then ∪ C_else ∪
                //       { Tcond == bool, T_then == T_else, T == T_then })
                //
                // For `if cond { then }` without an explicit else, we treat
                // it as `if cond { then } else ()`, so the overall type is
                // `unit` and the then-branch must also have type `unit`.
                let cond_ty = ctx.expr_ty_or_fresh(*cond);
                let then_ty = ctx.expr_ty_or_fresh(*then_branch);

                // Tcond == bool
                node.wanteds
                    .push(Constraint::eq(cond_ty, Ty::bool(), info.clone()));

                if let Some(else_id) = else_branch {
                    let else_ty = ctx.expr_ty_or_fresh(*else_id);

                    // T_then == T_else
                    node.wanteds
                        .push(Constraint::eq(then_ty.clone(), else_ty, info.clone()));

                    // T == T_then, where T is the overall if-expression type.
                    node.wanteds
                        .push(Constraint::eq(expr_ty, then_ty, info.clone()));
                } else {
                    // No else-branch: require that the then-branch has type
                    // unit and that the whole expression is unit.
                    node.wanteds
                        .push(Constraint::eq(then_ty.clone(), Ty::unit(), info.clone()));
                    node.wanteds
                        .push(Constraint::eq(expr_ty, Ty::unit(), info.clone()));
                }
            }
            ExprKind::IfPattern {
                scrutinee,
                pattern,
                then_branch,
                else_branch,
            } => {
                // Pattern-if, following the "Pattern-if" rule:
                //
                //   Γ ⊢ e ⇝ (Te, Ce)
                //   (pattern constraints, e.g. Te == nilable[T], x : T)
                //   Γ, Δ ⊢ e_then ⇝ (T_then, C_then)
                //   Γ ⊢ e_else ⇝ (T_else, C_else)
                //   ---------------------------------------------
                //   Γ ⊢ if pat = e { e_then } else { e_else } ⇝
                //       (T, Ce ∪ Cp ∪ C_then ∪ C_else ∪
                //           { T_then == T_else, T == T_then })
                apply_pattern_guard(pattern, *scrutinee, ctx, node, &info);

                let then_ty = ctx.expr_ty_or_fresh(*then_branch);
                if let Some(else_branch) = else_branch {
                    let else_ty = ctx.expr_ty_or_fresh(*else_branch);
                    node.wanteds
                        .push(Constraint::eq(then_ty.clone(), else_ty, info.clone()));
                    node.wanteds
                        .push(Constraint::eq(expr_ty, then_ty, info.clone()));
                } else {
                    node.wanteds
                        .push(Constraint::eq(then_ty.clone(), Ty::unit(), info.clone()));
                    node.wanteds
                        .push(Constraint::eq(expr_ty, Ty::unit(), info.clone()));
                }
            }
            ExprKind::While { cond, body } => {
                // While expressions (spec "While expressions"):
                //
                // Γ ⊢ cond ⇝ (Tcond, Ccond)
                // Γ ⊢ body ⇝ (Tbody, Cbody)
                // -------------------------------------------------
                // Γ ⊢ while cond { body } ⇝ (unit, Ccond ∪ Cbody ∪ { Tcond == bool })
                //
                // We generate:
                //   Tcond == bool
                //   expr_ty == unit
                let cond_ty = ctx.expr_ty_or_fresh(*cond);
                node.wanteds
                    .push(Constraint::eq(cond_ty, Ty::bool(), info.clone()));
                node.wanteds
                    .push(Constraint::eq(expr_ty, Ty::unit(), info.clone()));

                // Ensure the body has a type recorded, even though we do not
                // constrain it here; its internal constraints are generated
                // via recursion through expr_children.
                let _ = ctx.expr_ty_or_fresh(*body);
            }
            ExprKind::WhilePattern {
                scrutinee,
                pattern,
                body,
            } => {
                // Pattern-while, following the "Pattern-while" rule:
                //
                //   Γ ⊢ e ⇝ (Te, Ce)
                //   (pattern constraints, e.g. Te == nilable[T], x : T)
                //   Γ, Δ ⊢ body ⇝ (Tbody, Cbody)
                //   -------------------------------------------------
                //   Γ ⊢ while pat = e { body } ⇝ (unit, Ce ∪ Cp ∪ Cbody)
                apply_pattern_guard(pattern, *scrutinee, ctx, node, &info);

                let _body_ty = ctx.expr_ty_or_fresh(*body);
                node.wanteds
                    .push(Constraint::eq(expr_ty, Ty::unit(), info.clone()));
            }
            ExprKind::Loop { body } => {
                // Loop expressions (spec "Loop and break"):
                //
                // - Associate each `loop` with a fresh meta `?L` representing
                //   the loop's result type.
                // - Each `break e` inside the loop contributes an equality
                //   `Te == ?L`.
                // - The loop expression itself has type `?L` if any such break
                //   is reachable; otherwise it has type `never`. We model the
                //   result meta here and let later analysis decide reachability.
                let loop_ty = ctx.fresh_meta();
                ctx.push_loop_result(loop_ty.clone());

                let _body_ty = ctx.expr_ty_or_fresh(*body);

                // For now we always treat the loop as having type `?L`.
                node.wanteds
                    .push(Constraint::eq(expr_ty, loop_ty, info.clone()));

                ctx.pop_loop_result();
            }
            ExprKind::Break { expr } => {
                // Break expressions (spec "Loop and break"):
                //
                // Γ ⊢ e ⇝ (Te, C)
                // -----------------------------------------
                // Γ ⊢ break e ⇝ (never, C ∪ { Te == ?L })
                //
                // Bare `break` is treated as `break ()`.
                if let Some(loop_ty) = ctx.current_loop_result() {
                    if let Some(expr_id) = expr {
                        let break_ty = ctx.expr_ty_or_fresh(*expr_id);
                        node.wanteds
                            .push(Constraint::eq(break_ty, loop_ty, info.clone()));
                    } else {
                        node.wanteds
                            .push(Constraint::eq(Ty::unit(), loop_ty, info.clone()));
                    }
                }

                // The break expression itself has type `never`.
                node.wanteds
                    .push(Constraint::eq(expr_ty, Ty::Never, info.clone()));
            }
            ExprKind::Continue => {
                // Continue expressions have type `never` and do not constrain
                // any ambient types beyond control flow (spec "Loop and break").
                node.wanteds
                    .push(Constraint::eq(expr_ty, Ty::Never, info.clone()));
            }
            ExprKind::Return { expr: ret_expr } => {
                // Return expressions (spec "Return expressions"):
                //
                // Γ ⊢ e ⇝ (Te, C)
                // -------------------------------------------------
                // Γ ⊢ return e ⇝ (never, C ∪ { Te == Tret })
                //
                // We require the current function result type `Tret` to be
                // available from the context (pushed by the caller).
                if let Some(ret_ty) = ctx.current_fn_ret() {
                    let value_ty = if let Some(ret_expr) = ret_expr {
                        ctx.expr_ty_or_fresh(*ret_expr)
                    } else {
                        Ty::unit()
                    };
                    node.wanteds
                        .push(Constraint::eq(value_ty, ret_ty, info.clone()));
                }

                // The return expression itself has type `never`.
                node.wanteds
                    .push(Constraint::eq(expr_ty, Ty::Never, info.clone()));
            }
            ExprKind::For {
                pattern,
                iter_expr,
                body,
            } => {
                // For loops (spec "For loops"):
                //
                //   for pat in e { body }
                //
                // use traits Iterable[Container, Iter, Elem] and Iter[Iter, Elem]
                // relating a container to an iterator state and element type.
                //
                // Γ ⊢ e ⇝ (Te, Ce)
                // fresh It
                // fresh Elem
                // -------------------------------------------------
                // Γ ⊢ for pat in e { body } ⇝
                //   (unit, Ce ∪ Cbody ∪ { Iterable[Te, It, Elem], Iter[It, Elem] } ∪ pattern/body constraints)

                let iter_ty = ctx.expr_ty_or_fresh(*iter_expr);
                let it_ty = ctx.fresh_meta();
                let elem_ty = ctx.fresh_meta();

                let iterable_trait_fqn = ctx.env().resolve_builtin("Iterable");
                let iter_trait_fqn = ctx.env().resolve_builtin("Iter");

                // Iterable[Te, It, Elem]
                node.wanteds.push(Constraint::class(
                    iterable_trait_fqn,
                    vec![iter_ty, it_ty.clone(), elem_ty.clone()],
                    info.clone(),
                ));

                // Iter[It, Elem]
                node.wanteds.push(Constraint::class(
                    iter_trait_fqn,
                    vec![it_ty, elem_ty.clone()],
                    info.clone(),
                ));

                // Pattern binds element type into the loop body environment.
                apply_pattern_guard_with_ty(pattern, elem_ty, ctx, node, &info);

                let _body_ty = ctx.expr_ty_or_fresh(*body);
                node.wanteds
                    .push(Constraint::eq(expr_ty, Ty::unit(), info.clone()));
            }
            ExprKind::Call { callee, args } => {
                // Calls. Special case `recv.method(args...)` (lowered as
                // `Call(FieldAccess { recv, field }, args)`) as a trait
                // method call rather than a struct field access.
                if let Some(ExprKind::FieldAccess { recv, field }) =
                    input.expr_kind(*callee).cloned()
                {
                    // Collect types for explicit arguments.
                    let mut explicit_arg_tys = Vec::with_capacity(args.len());
                    for arg_expr in args {
                        let arg_ty = ctx.expr_ty_or_fresh(*arg_expr);
                        explicit_arg_tys.push(arg_ty);
                    }

                    let recv_ty = ctx.expr_ty_or_fresh(recv);
                    log::debug!("[generate_constraints_for_expr] recv_ty = {}", recv_ty);

                    // Even though we do not recurse into the `FieldAccess` callee node (to
                    // avoid generating `HasField`), downstream passes still expect the
                    // callee expression to have a type. Record it as a function type:
                    //
                    //   recv.method(args...) : (Trecv, Targs...) -> Tret
                    //
                    let recv_param_ty = ctx.fresh_meta();
                    let mut callee_arg_tys = Vec::with_capacity(explicit_arg_tys.len() + 1);
                    callee_arg_tys.push(recv_param_ty);
                    callee_arg_tys.extend(explicit_arg_tys.iter().cloned());
                    let expected_fn_ty = Ty::Func(callee_arg_tys, Box::new(expr_ty.clone()));
                    ctx.expr_types.insert(*callee, expected_fn_ty.clone());

                    // Do not attempt to resolve methods during constraint generation.
                    //
                    // The receiver type is frequently still a meta variable at this phase
                    // (even in the presence of annotations), and global-by-name lookup is
                    // ambiguous once multiple traits or inherent impls share method names.
                    //
                    // Instead, emit a deferred `ResolveCall` constraint and let the solver
                    // rewrite it into existing constraints (Instantiate/Eq/Recv) once the
                    // receiver/LHS type becomes headed.
                    node.wanteds.push(Constraint {
                        kind: ConstraintKind::ResolveCall(ResolveCallConstraint::new_instance(
                            recv_ty,
                            field,
                            expected_fn_ty,
                        )),
                        info: info.clone(),
                    });

                    // Recurse into receiver and explicit args, but do not recurse into
                    // the callee `FieldAccess` node (which would generate `HasField`).
                    for child_expr in std::iter::once(recv).chain(args.iter().copied()) {
                        generate_constraints_for_child(
                            input,
                            ctx,
                            node,
                            def_id,
                            skolem_subst,
                            next_id,
                            child_expr,
                        );
                    }

                    // Return here so we don't recurse via `expr_children` again.
                    return;
                }

                // Also treat `T::method(args...)` / `T[...]::method(args...)` as a deferred
                // member call. The callee is lowered as `ScopedAccess { def_id, lhs_ty }`.
                if let Some(ExprKind::ScopedAccess {
                    def_id,
                    member_name,
                    lhs_ty,
                }) = input.expr_kind(*callee).cloned()
                {
                    // Collect types for explicit arguments.
                    let mut explicit_arg_tys = Vec::with_capacity(args.len());
                    for arg_expr in args {
                        let arg_ty = ctx.expr_ty_or_fresh(*arg_expr);
                        explicit_arg_tys.push(arg_ty);
                    }

                    // Downstream passes still expect the callee expression to
                    // have a type. Record it as a function type:
                    //
                    //   T::member(args...) : (Targs...) -> Tret
                    //
                    let expected_fn_ty =
                        Ty::Func(explicit_arg_tys.clone(), Box::new(expr_ty.clone()));
                    ctx.expr_types.insert(*callee, expected_fn_ty.clone());

                    let receiver_subst = skolem_subst.and_then(|skolem_subst| {
                        let mut lhs_vars = HashSet::new();
                        lhs_ty.free_ty_vars(&mut lhs_vars);

                        let mut subst = Subst::new();
                        for var in lhs_vars {
                            if let Some(ty) = skolem_subst.get(&var) {
                                subst.insert(var, ty.clone());
                            }
                        }

                        if subst.is_empty() { None } else { Some(subst) }
                    });

                    node.wanteds.push(Constraint {
                        kind: ConstraintKind::ResolveCall(ResolveCallConstraint::new_scoped(
                            lhs_ty,
                            def_id,
                            expected_fn_ty,
                            member_name,
                            receiver_subst,
                        )),
                        info: info.clone(),
                    });

                    // Recurse into explicit args, but do not recurse into the callee
                    // `ScopedAccess` node (which would instantiate the binding scheme).
                    for child_expr in args.iter().copied() {
                        generate_constraints_for_child(
                            input,
                            ctx,
                            node,
                            def_id,
                            skolem_subst,
                            next_id,
                            child_expr,
                        );
                    }

                    // Return here so we don't recurse via `expr_children` again.
                    return;
                }

                // Generic call: relate the callee's type and the call result
                // type via a function type: (arg_tys...) -> expr_ty.
                let mut arg_tys = vec![];
                for arg_expr in args {
                    let arg_ty = ctx.expr_ty_or_fresh(*arg_expr);
                    arg_tys.push(arg_ty);
                }

                let callee_ty = ctx.expr_ty_or_fresh(*callee);

                let func_ty = Ty::Func(arg_tys, Box::new(expr_ty));

                node.wanteds.push(Constraint::eq(callee_ty, func_ty, info));
            }
        }
    }

    // Recurse into children based on the ModuleInput's view of the AST.
    for child_expr in input.expr_children(expr) {
        generate_constraints_for_child(input, ctx, node, def_id, skolem_subst, next_id, child_expr);
    }
}

fn generate_constraints_for_child(
    input: &TypeCheckInput,
    ctx: &mut SolverContext<'_>,
    node: &mut ConstraintNode,
    def_id: DefId,
    skolem_subst: Option<&Subst>,
    next_id: &mut u32,
    child_expr: NodeId,
) {
    let child_id = ConstraintNodeId(*next_id);
    *next_id += 1;
    let mut child_node = ConstraintNode::new(child_id);
    generate_constraints_for_expr(
        input,
        ctx,
        def_id,
        skolem_subst,
        child_expr,
        &mut child_node,
        next_id,
    );
    node.children.push(child_node);
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, collections::HashMap, rc::Rc};

    use ray_shared::{
        def::DefId,
        file_id::FileId,
        local_binding::LocalBindingId,
        node_id::NodeId,
        ty::{SchemaVarAllocator, Ty},
    };

    use crate::{
        BindingKind, BindingRecord, ExprRecord, TypeCheckInput,
        binding_groups::{BindingGraph, BindingGroup},
        constraint_tree::{ConstraintNode, build_constraint_tree_for_group, walk_tree},
        constraints::ConstraintKind,
        context::{ExprKind, Pattern, SolverContext},
        mocks::MockTypecheckEnv,
        types::TyScheme,
    };

    fn single_binding_group(def_id: DefId) -> BindingGroup<DefId> {
        BindingGroup::new(vec![def_id])
    }

    fn make_input(
        def_id: DefId,
        root_expr: NodeId,
        kinds: HashMap<NodeId, ExprKind>,
    ) -> TypeCheckInput {
        let mut graph = BindingGraph::<DefId>::new();
        graph.add_binding(def_id);

        let mut binding_records = HashMap::new();
        let mut record = BindingRecord::new(BindingKind::Value);
        record.body_expr = Some(root_expr);
        binding_records.insert(def_id, record);

        let expr_records = kinds
            .into_iter()
            .map(|(expr_id, kind)| (expr_id, ExprRecord { kind, source: None }))
            .collect();

        TypeCheckInput {
            bindings: graph,
            binding_records,
            node_bindings: HashMap::new(),
            expr_records,
            pattern_records: HashMap::new(),
            schema_allocator: Rc::new(RefCell::new(SchemaVarAllocator::new())),
            lowering_errors: Vec::new(),
        }
    }

    fn make_function_input(
        def_id: DefId,
        params: Vec<LocalBindingId>,
        func_expr: NodeId,
        root_expr: NodeId,
        kind: ExprKind,
    ) -> TypeCheckInput {
        let mut graph = BindingGraph::<DefId>::new();
        graph.add_binding(def_id);

        let mut binding_records = HashMap::new();
        let mut record = BindingRecord::new(BindingKind::Function {
            params: params.clone(),
        });
        record.body_expr = Some(func_expr);
        binding_records.insert(def_id, record);

        let mut expr_records = HashMap::new();
        expr_records.insert(root_expr, ExprRecord { kind, source: None });
        expr_records.insert(
            func_expr,
            ExprRecord {
                kind: ExprKind::Function {
                    params,
                    body: root_expr,
                },
                source: None,
            },
        );

        TypeCheckInput {
            bindings: graph,
            binding_records,
            node_bindings: HashMap::new(),
            expr_records,
            pattern_records: HashMap::new(),
            schema_allocator: Rc::new(RefCell::new(SchemaVarAllocator::new())),
            lowering_errors: Vec::new(),
        }
    }

    fn get_binding_node(tree: &ConstraintNode) -> &ConstraintNode {
        // Root node id is 0; binding nodes are its children.
        assert_eq!(tree.id.0, 0);
        assert_eq!(tree.children.len(), 1);
        &tree.children[0]
    }

    #[test]
    fn literal_int_generates_int_class_constraint() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(expr_id, ExprKind::LiteralInt);

        let input = make_input(def_id, expr_id, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        assert_eq!(binding_node.wanteds.len(), 2);
        // One equality tying binding type to expr type, and one Int predicate.
        assert!(
            binding_node
                .wanteds
                .iter()
                .any(|c| matches!(c.kind, crate::constraints::ConstraintKind::Class(_)))
        );
    }

    #[test]
    fn literal_float_generates_float_class_constraint() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(expr_id, ExprKind::LiteralFloat);

        let input = make_input(def_id, expr_id, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        assert!(
            binding_node
                .wanteds
                .iter()
                .any(|c| matches!(c.kind, crate::constraints::ConstraintKind::Class(_)))
        );
    }

    #[test]
    fn literal_bool_is_constrained_to_bool() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(expr_id, ExprKind::LiteralBool(true));

        let input = make_input(def_id, expr_id, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        assert!(
            binding_node
                .wanteds
                .iter()
                .any(|c| matches!(c.kind, ConstraintKind::Eq(_)))
        );
    }

    #[test]
    fn some_literal_generates_nilable_equality() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let inner_id = NodeId::new();
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(inner_id, ExprKind::LiteralInt);
        kinds.insert(expr_id, ExprKind::Some { expr: inner_id });

        let input = make_input(def_id, expr_id, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        assert!(binding_node.wanteds.iter().any(|c| match &c.kind {
            ConstraintKind::Eq(eq) =>
                matches!(eq.lhs, Ty::Proj(_, _)) || matches!(eq.rhs, Ty::Proj(_, _)),
            _ => false,
        }));
    }

    #[test]
    fn nil_literal_generates_nilable_equality() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(expr_id, ExprKind::Nil);

        let input = make_input(def_id, expr_id, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        assert!(binding_node.wanteds.iter().any(|c| match &c.kind {
            ConstraintKind::Eq(eq) =>
                matches!(eq.lhs, Ty::Proj(_, _)) || matches!(eq.rhs, Ty::Proj(_, _)),
            _ => false,
        }));
    }

    #[test]
    fn var_uses_binding_scheme() {
        let def_id = DefId::new(FileId(0), 0);
        let local_binding_id = LocalBindingId::new(def_id, 6);
        let _guard = NodeId::enter_def(def_id);
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(expr_id, ExprKind::LocalRef(local_binding_id));

        let input = make_input(def_id, expr_id, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let scheme_ty = Ty::int();
        ctx.binding_schemes.insert(
            local_binding_id.into(),
            TyScheme::from_mono(scheme_ty.clone()),
        );

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        // BindingRef now generates an InstantiateConstraint for local bindings
        assert!(binding_node.wanteds.iter().any(|c| match &c.kind {
            ConstraintKind::Instantiate(inst) => {
                matches!(inst.target, crate::constraints::InstantiateTarget::Local(bid) if bid == local_binding_id)
            }
            _ => false,
        }));
    }

    #[test]
    fn struct_literal_generates_struct_and_hasfield() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let field_expr = NodeId::new();
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(field_expr, ExprKind::LiteralInt);
        kinds.insert(
            expr_id,
            ExprKind::StructLiteral {
                path: "A".into(),
                fields: vec![("x".to_string(), field_expr)],
            },
        );

        let input = make_input(def_id, expr_id, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        assert!(
            binding_node
                .wanteds
                .iter()
                .any(|c| matches!(c.kind, ConstraintKind::Eq(_)))
        );
        assert!(
            binding_node
                .wanteds
                .iter()
                .any(|c| matches!(c.kind, ConstraintKind::HasField(_)))
        );
    }

    #[test]
    fn field_access_generates_hasfield_predicate() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let recv_expr = NodeId::new();
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(
            recv_expr,
            ExprKind::StructLiteral {
                path: "A".into(),
                fields: vec![],
            },
        );
        kinds.insert(
            expr_id,
            ExprKind::FieldAccess {
                recv: recv_expr,
                field: "x".to_string(),
            },
        );

        let input = make_input(def_id, expr_id, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        assert!(
            binding_node
                .wanteds
                .iter()
                .any(|c| matches!(c.kind, ConstraintKind::HasField(_)))
        );
    }

    #[test]
    fn if_generates_expected_equalities() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let cond = NodeId::new();
        let then_expr = NodeId::new();
        let else_expr = NodeId::new();
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(cond, ExprKind::LiteralBool(true));
        kinds.insert(then_expr, ExprKind::LiteralInt);
        kinds.insert(else_expr, ExprKind::LiteralInt);
        kinds.insert(
            expr_id,
            ExprKind::If {
                cond,
                then_branch: then_expr,
                else_branch: Some(else_expr),
            },
        );

        let input = make_input(def_id, expr_id, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        assert!(
            binding_node
                .wanteds
                .iter()
                .filter(|c| matches!(c.kind, ConstraintKind::Eq(_)))
                .count()
                >= 2
        );
    }

    #[test]
    fn if_pattern_some_applies_pattern_guard() {
        let def_id = DefId::new(FileId(0), 0);
        let local_binding_id = LocalBindingId::new(def_id, 10);
        let _guard = NodeId::enter_def(def_id);
        let scrutinee = NodeId::new();
        let then_expr = NodeId::new();
        let else_expr = NodeId::new();
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(scrutinee, ExprKind::Nil);
        kinds.insert(then_expr, ExprKind::LiteralInt);
        kinds.insert(else_expr, ExprKind::LiteralInt);
        kinds.insert(
            expr_id,
            ExprKind::IfPattern {
                scrutinee,
                pattern: Pattern::Some(local_binding_id),
                then_branch: then_expr,
                else_branch: Some(else_expr),
            },
        );

        let input = make_input(def_id, expr_id, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        assert!(binding_node.wanteds.iter().any(|c| match &c.kind {
            ConstraintKind::Eq(eq) =>
                matches!(eq.lhs, Ty::Proj(_, _)) || matches!(eq.rhs, Ty::Proj(_, _)),
            _ => false,
        }));
        assert!(ctx.binding_schemes.contains_key(&local_binding_id.into()));
    }

    #[test]
    fn while_generates_bool_and_unit_constraints() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let cond = NodeId::new();
        let body = NodeId::new();
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(cond, ExprKind::LiteralBool(true));
        kinds.insert(body, ExprKind::LiteralInt);
        kinds.insert(expr_id, ExprKind::While { cond, body });

        let input = make_input(def_id, expr_id, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        assert!(
            binding_node
                .wanteds
                .iter()
                .any(|c| matches!(c.kind, ConstraintKind::Eq(_)))
        );
    }

    #[test]
    fn loop_and_break_contribute_loop_result_constraint() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let break_expr = NodeId::new();
        let loop_expr = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(break_expr, ExprKind::LiteralInt);
        kinds.insert(loop_expr, ExprKind::Loop { body: break_expr });

        let input = make_input(def_id, loop_expr, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        assert!(
            binding_node
                .wanteds
                .iter()
                .any(|c| matches!(c.kind, ConstraintKind::Eq(_)))
        );
    }

    #[test]
    fn return_uses_current_function_result_type() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let func_expr = NodeId::new();
        let ret_expr = NodeId::new();
        let body_expr = NodeId::new();

        let mut input = make_function_input(
            def_id,
            Vec::new(),
            func_expr,
            body_expr,
            ExprKind::Return {
                expr: Some(ret_expr),
            },
        );
        // Attach the literal as a separate binding so constraint generation
        // can look up its type.
        input.expr_records.insert(
            ret_expr,
            ExprRecord {
                kind: ExprKind::LiteralInt,
                source: None,
            },
        );

        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        ctx.binding_schemes.insert(
            def_id.into(),
            TyScheme::from_mono(Ty::func(vec![], Ty::int())),
        );

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);
        walk_tree(&tree, &mut |item| println!("{}", item));

        assert!(binding_node.wanteds.iter().any(|c| match &c.kind {
            ConstraintKind::Eq(eq) => {
                if let Ty::Func(_, ret_ty) = &eq.lhs {
                    **ret_ty == Ty::int()
                } else if let Ty::Func(_, ret_ty) = &eq.rhs {
                    **ret_ty == Ty::int()
                } else {
                    false
                }
            }
            _ => false,
        }));
    }

    #[test]
    fn for_loop_generates_iter_constraint() {
        let def_id = DefId::new(FileId(0), 0);
        let local_binding_id = LocalBindingId::new(def_id, 14);
        let _guard = NodeId::enter_def(def_id);
        let iter_expr = NodeId::new();
        let body_expr = NodeId::new();
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(iter_expr, ExprKind::LiteralInt);
        kinds.insert(body_expr, ExprKind::LiteralInt);
        kinds.insert(
            expr_id,
            ExprKind::For {
                pattern: Pattern::Binding(local_binding_id),
                iter_expr,
                body: body_expr,
            },
        );

        let input = make_input(def_id, expr_id, kinds);
        let group = single_binding_group(def_id);
        let typecheck_env = MockTypecheckEnv::new();
        let mut ctx = SolverContext::new(Rc::default(), &typecheck_env);

        let tree = build_constraint_tree_for_group(&input, &mut ctx, &group);
        let binding_node = get_binding_node(&tree);

        assert!(
            binding_node
                .wanteds
                .iter()
                .any(|c| matches!(c.kind, ConstraintKind::Class(_)))
        );
    }
}

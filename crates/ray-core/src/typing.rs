use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use ray_shared::{
    def::DefId,
    local_binding::LocalBindingId,
    node_id::NodeId,
    pathlib::Path,
    resolution::{DefTarget, Resolution},
    ty::{SchemaVarAllocator, Ty},
};
use ray_typing::{
    BindingKind, BindingRecord, ExprRecord, NodeBinding, PatternKind, PatternRecord,
    TypeCheckInput, TypeError,
    binding_groups::{BindingGraph, BindingId},
    context::{AssignLhs, ExprKind, LhsPattern, Pattern},
    env::TypecheckEnv,
    info::TypeSystemInfo,
};

use crate::{
    ast::{
        CurlyElement, Decl, Expr, FnParam, Literal, Module, Node, Pattern as AstPattern,
        RangeLimits,
    },
    passes::binding::BindingPassOutput,
    sourcemap::SourceMap,
};

struct TyLowerCtx<'a> {
    srcmap: &'a SourceMap,
    env: &'a dyn TypecheckEnv,
    resolutions: &'a HashMap<NodeId, Resolution>,
    binding_records: HashMap<BindingId, BindingRecord>,
    node_bindings: HashMap<NodeId, NodeBinding>,
    expr_records: HashMap<NodeId, ExprRecord>,
    pattern_records: HashMap<NodeId, PatternRecord>,
    /// Mapping from fully-qualified value paths to their BindingId, used to
    /// lower Expr::Name / Expr::Path into ExprKind::Var, and later to
    /// reconstruct per-binding schemes keyed by their module path.
    value_bindings: HashMap<Path, BindingId>,
    /// Stack of local scopes for value bindings introduced within function
    /// bodies (e.g. via assignment). Each scope maps a simple name to a
    /// BindingId; lookup walks the stack from innermost to outermost.
    local_scopes: Vec<HashMap<Path, BindingId>>,
    loop_depth: usize,
    errors: Vec<TypeError>,
}

impl<'a> TyLowerCtx<'a> {
    fn new(
        srcmap: &'a SourceMap,
        env: &'a dyn TypecheckEnv,
        binding_output: &BindingPassOutput,
        resolutions: &'a HashMap<NodeId, Resolution>,
    ) -> Self {
        TyLowerCtx {
            srcmap,
            env,
            resolutions,
            binding_records: binding_output.binding_records.clone(),
            node_bindings: binding_output.node_bindings.clone(),
            expr_records: HashMap::new(),
            pattern_records: HashMap::new(),
            value_bindings: binding_output.value_bindings.clone(),
            local_scopes: vec![],
            loop_depth: 0,
            errors: Vec::new(),
        }
    }

    fn expr_id<T>(&self, node: &Node<T>) -> NodeId {
        node.id
    }

    fn record_expr<T>(&mut self, node: &Node<T>, kind: ExprKind) -> NodeId {
        let id = self.expr_id(node);
        let source = self.srcmap.get_by_id(node.id);
        self.expr_records.insert(id, ExprRecord { kind, source });
        id
    }

    fn record_pattern<T>(&mut self, node: &Node<T>, kind: PatternKind) {
        let id = self.expr_id(node);
        let source = self.srcmap.get_by_id(node.id);
        self.pattern_records
            .insert(id, PatternRecord { kind, source });
    }

    fn enter_scope(&mut self) {
        self.local_scopes.push(HashMap::new());
    }

    fn exit_scope(&mut self) {
        self.local_scopes.pop();
    }

    fn enter_loop(&mut self) {
        self.loop_depth += 1;
    }

    fn exit_loop(&mut self) {
        self.loop_depth = self.loop_depth.saturating_sub(1);
    }

    fn insert_local_binding(&mut self, path: Path, binding: BindingId) {
        if let Some(scope) = self.local_scopes.last_mut() {
            scope.insert(path, binding);
        }
    }

    fn resolve_local(&self, path: &Path) -> Option<BindingId> {
        for scope in self.local_scopes.iter().rev() {
            if let Some(binding) = scope.get(path) {
                return Some(*binding);
            }
        }
        None
    }

    fn binding_from_node_or_path(&mut self, node_id: NodeId, path: &Path) -> BindingId {
        if let Some(existing) = self.node_bindings.get(&node_id).copied() {
            let binding = existing.binding();
            self.insert_local_binding(path.clone(), binding);
            binding
        } else if let Some(existing) = self.resolve_local(path) {
            existing
        } else if let Some(existing) = self.value_bindings.get(path).copied() {
            self.insert_local_binding(path.clone(), existing);
            existing
        } else {
            log::warn!("missing binding for `{}` (node {:#x})", path, node_id);
            BindingId(0)
        }
    }

    fn note_binding_source(&mut self, binding: BindingId, node_id: NodeId) {
        if let Some(src) = self.srcmap.get_by_id(node_id) {
            self.binding_records
                .entry(binding)
                .or_insert_with(|| BindingRecord::new(BindingKind::Value))
                .sources
                .push(src);
        }
    }

    fn emit_error(&mut self, node: &Node<Expr>, msg: impl Into<String>) {
        let mut info = TypeSystemInfo::new();
        if let Some(src) = self.srcmap.get_by_id(node.id) {
            info.with_src(src);
        }
        self.errors.push(TypeError::message(msg, info));
    }

    fn emit_missing_binding(&mut self, node_id: NodeId, what: &str) {
        let mut info = TypeSystemInfo::new();
        if let Some(src) = self.srcmap.get_by_id(node_id) {
            info.with_src(src);
        }
        self.errors.push(TypeError::message(
            format!("missing binding for {}", what),
            info,
        ));
    }
}

/// Collect DefIds from module declarations that produce value bindings.
pub fn collect_def_ids(module: &Module<(), Decl>) -> Vec<DefId> {
    let mut all_defs: Vec<DefId> = Vec::new();

    for decl_node in &module.decls {
        match &decl_node.value {
            Decl::Func(func) if func.body.is_some() => {
                all_defs.push(decl_node.id.owner);
            }
            Decl::Declare(_) => {
                all_defs.push(decl_node.id.owner);
            }
            Decl::Extern(_) => {
                all_defs.push(decl_node.id.owner);
            }
            Decl::Impl(im) => {
                if let Some(funcs) = &im.funcs {
                    for func_node in funcs {
                        if func_node.value.body.is_some() {
                            all_defs.push(func_node.id.owner);
                        }
                    }
                }
                if let Some(consts) = &im.consts {
                    for const_node in consts {
                        all_defs.push(const_node.id.owner);
                    }
                }
            }
            _ => {}
        }
    }

    all_defs
}

/// Build DefId-keyed binding records from the legacy BindingId-keyed records.
pub fn build_def_binding_records(
    binding_output: &BindingPassOutput,
) -> HashMap<DefId, BindingRecord> {
    let mut def_binding_records: HashMap<DefId, BindingRecord> = HashMap::new();
    for (binding_id, record) in &binding_output.binding_records {
        for (node_id, node_binding) in &binding_output.node_bindings {
            if let NodeBinding::Def(bid) = node_binding {
                if bid == binding_id {
                    def_binding_records.insert(node_id.owner, record.clone());
                    break;
                }
            }
        }
    }
    def_binding_records
}

pub fn build_typecheck_input(
    decls: &[Node<Decl>],
    _top_level_stmts: &[Node<Expr>],
    srcmap: &SourceMap,
    env: &dyn TypecheckEnv,
    binding_output: &BindingPassOutput,
    resolutions: &HashMap<NodeId, Resolution>,
    def_bindings: BindingGraph<DefId>,
    def_binding_records: HashMap<DefId, BindingRecord>,
    schema_allocator: Rc<RefCell<SchemaVarAllocator>>,
) -> TypeCheckInput {
    let mut ctx = TyLowerCtx::new(srcmap, env, binding_output, resolutions);

    // TODO: handle top-level statements

    // For now, treat each function declaration with a body as a separate
    // binding whose root expression is the function body. This matches the
    // "value bindings" in docs/type-system.md and is sufficient for early
    // end-to-end tests. Other declaration kinds are enumerated explicitly
    // below so that we do not silently ignore anything.
    for decl_node in decls {
        match &decl_node.value {
            Decl::Func(func) => {
                if let Some(body) = &func.body {
                    lower_func_binding(&mut ctx, decl_node.id, &func.sig, &body);
                }
                // Function declarations without bodies (if they ever occur) do
                // not introduce value bindings; they contribute only to the
                // nominal environment via GlobalEnv.
            }
            // Standalone function signatures are lowered elsewhere (e.g. via
            // associated functions or extern declarations) and do not create
            // value bindings by themselves.
            Decl::FnSig(_) => {}
            // Structs/traits/type aliases are already lowered into the
            // GlobalEnv by the AST lowering pipeline; they do not produce
            // value bindings here.
            Decl::Struct(_) | Decl::Trait(_) | Decl::TypeAlias(_, _) => {}
            // Impl blocks can contain methods and consts that introduce
            // additional value bindings. We lower these similarly to
            // top-level functions and declarations so they participate in
            // constraint generation.
            Decl::Impl(im) => {
                // Methods inside the impl.
                if let Some(funcs) = &im.funcs {
                    for func_node in funcs {
                        let func = &func_node.value;
                        if let Some(body) = &func.body {
                            lower_func_binding(&mut ctx, func_node.id, &func.sig, body);
                        }
                    }
                }

                // Consts inside the impl.
                if let Some(consts) = &im.consts {
                    for assign_node in consts {
                        match &assign_node.lhs.value {
                            AstPattern::Name(_) => {
                                if let Some(NodeBinding::Def(_)) =
                                    ctx.node_bindings.get(&assign_node.id).copied()
                                {
                                    let _root_expr_id = lower_expr(&mut ctx, &assign_node.rhs);
                                } else {
                                    ctx.emit_missing_binding(assign_node.id, "impl const");
                                }
                            }
                            _ => {
                                todo!(
                                    "lowering for impl consts with non-name patterns into ModuleInput"
                                );
                            }
                        }
                    }
                }
            }
            // Top-level `let`-style declarations. For now we only handle the
            // simplest form `let x = e` where `x` is a single name pattern;
            // more complex patterns are left as explicit TODOs so that
            // constraint generation remains aligned with the spec.
            Decl::Declare(assign) => {
                match &assign.lhs.value {
                    AstPattern::Name(_) => {
                        if let Some(NodeBinding::Def(_)) = ctx.node_bindings.get(&decl_node.id) {
                            let _root_expr_id = lower_expr(&mut ctx, &assign.rhs);
                        } else {
                            ctx.emit_missing_binding(decl_node.id, "top-level declaration");
                        }
                    }
                    // Destructuring and other complex patterns will be wired
                    // in once the corresponding spec rules are implemented.
                    _ => {
                        todo!(
                            "lowering for top-level declarations with non-name patterns into ModuleInput"
                        );
                    }
                }
            }
            // Extern declarations provide signatures (often intrinsics) that
            // need bindings so they can be referenced in expressions.
            Decl::Extern(ext) => {
                let inner_decl = ext.decl_node();
                if let Decl::FnSig(sig) = &inner_decl.value {
                    lower_signature_binding(&mut ctx, decl_node.id, inner_decl.id, sig);
                }
            }
            Decl::Mutable(_) | Decl::Name(_) => {
                // TODO: lower declaration-only bindings into value bindings
                // once their typing rules are specified.
            }
        }
    }

    TypeCheckInput {
        bindings: def_bindings,
        binding_records: def_binding_records,
        node_bindings: ctx.node_bindings,
        expr_records: ctx.expr_records,
        pattern_records: ctx.pattern_records,
        schema_allocator,
        lowering_errors: ctx.errors,
    }
}

fn lower_func_binding(
    ctx: &mut TyLowerCtx<'_>,
    decl_id: NodeId,
    sig: &crate::ast::FuncSig,
    body: &Node<Expr>,
) {
    let binding_id = match ctx.node_bindings.get(&decl_id) {
        Some(node_binding) => node_binding.binding(),
        None => {
            ctx.emit_missing_binding(decl_id, "function");
            return;
        }
    };

    let mut param_bindings: Vec<LocalBindingId> = Vec::with_capacity(sig.params.len());

    // If this function has an already-resolved type scheme on the v1 side,
    // convert it into the new TyScheme and seed the binding schemes with it.
    // This implements the "use function annotated type" rule: the annotated
    // type constrains the body, and generalization will reproduce the same
    // scheme (up to residual predicates).
    if let Some(scheme) = &sig.ty {
        if let Some(rec) = ctx.binding_records.get_mut(&binding_id) {
            rec.scheme = Some(scheme.clone());
        }
    }

    // Each function body gets its own local scope for bindings introduced
    // by parameters, assignments, and other local-binding forms.
    ctx.enter_scope();
    // Seed the local scope with bindings for function parameters so that
    // parameter uses lower to ExprKind::Var.
    for param_node in &sig.params {
        // Get LocalBindingId from resolutions (set by name resolution phase)
        let local_id = match ctx.resolutions.get(&param_node.id) {
            Some(Resolution::Local(local_id)) => *local_id,
            _ => {
                // Fallback: create a placeholder LocalBindingId if not resolved
                log::warn!("Parameter {:?} not found in resolutions", param_node.id);
                continue;
            }
        };

        // Also record in legacy binding system for backwards compatibility
        match &param_node.value {
            FnParam::Name(n) => {
                let binding = ctx.binding_from_node_or_path(param_node.id, &n.path);
                ctx.note_binding_source(binding, param_node.id);
            }
            FnParam::DefaultValue(p, _) => {
                let binding = ctx.binding_from_node_or_path(param_node.id, p.name());
                ctx.note_binding_source(binding, param_node.id);
            }
            FnParam::Missing { placeholder, .. } => {
                let binding = ctx.binding_from_node_or_path(param_node.id, &placeholder.path);
                ctx.note_binding_source(binding, param_node.id);
            }
        }
        param_bindings.push(local_id);
    }
    if let Some(rec) = ctx.binding_records.get_mut(&binding_id) {
        rec.kind = BindingKind::Function {
            params: param_bindings.clone(),
        };
    }
    let body_expr_id = lower_expr(ctx, body);
    ctx.exit_scope();

    let source = ctx.srcmap.get_by_id(decl_id);
    ctx.expr_records.insert(
        decl_id,
        ExprRecord {
            kind: ExprKind::Function {
                params: param_bindings,
                body: body_expr_id,
            },
            source,
        },
    );
}

fn lower_signature_binding(
    ctx: &mut TyLowerCtx<'_>,
    extern_decl_id: NodeId,
    sig_decl_id: NodeId,
    sig: &crate::ast::FuncSig,
) {
    let binding_id = match ctx.node_bindings.get(&sig_decl_id) {
        Some(node_binding) => node_binding.binding(),
        None => {
            ctx.emit_missing_binding(sig_decl_id, "extern signature");
            return;
        }
    };
    ctx.node_bindings
        .insert(extern_decl_id, NodeBinding::Def(binding_id));

    if let Some(record) = ctx.binding_records.get_mut(&binding_id) {
        if let Some(scheme) = &sig.ty {
            record.scheme = Some(scheme.clone());
        }
    }
}

/// Lower an assignment left-hand-side pattern (docs/type-system.md A.7, A.8)
/// into the simplified `AssignLhs` form used by the type system.
///
/// This currently supports:
/// - Simple name patterns `x = rhs`.
/// - Deref patterns `*x = rhs` where `x` is a simple name.
/// - Field patterns `x.field = rhs` where `x` is a simple name.
/// - Tuple / sequence destructuring where each element is a simple name,
///   e.g. `(a, b) = rhs` or `a, b = rhs`.
///
/// More complex patterns (nested destructuring, struct patterns, `some(...)`
/// on the left-hand side) are left as explicit TODOs.
fn lower_pattern(ctx: &mut TyLowerCtx<'_>, pat: &Node<AstPattern>) -> LhsPattern {
    match &pat.value {
        AstPattern::Name(name) => {
            // Get LocalBindingId from resolutions
            let local_id = match ctx.resolutions.get(&pat.id) {
                Some(Resolution::Local(local_id)) => *local_id,
                _ => {
                    // Fallback for unresolved patterns - should not happen in valid code
                    log::warn!("Pattern {:?} not found in resolutions", pat.id);
                    // Still record in legacy system for backwards compatibility
                    let _binding = ctx.binding_from_node_or_path(pat.id, &name.path);
                    ctx.record_pattern(pat, PatternKind::Missing);
                    return LhsPattern::Binding(LocalBindingId::new(
                        DefId::new(ray_shared::file_id::FileId(0), 0),
                        0,
                    ));
                }
            };
            // Also record in legacy binding system
            ctx.record_pattern(pat, PatternKind::Binding { binding: local_id });
            LhsPattern::Binding(local_id)
        }
        AstPattern::Sequence(items) | AstPattern::Tuple(items) => {
            // Destructuring pattern `p1, p2, ...` or `(p1, p2, ...)`, which
            // is typed structurally via the tuple pattern rule in A.7.
            let mut elements = Vec::with_capacity(items.len());
            let mut child_ids = Vec::with_capacity(items.len());
            for item in items {
                elements.push(lower_pattern(ctx, item));
                child_ids.push(ctx.expr_id(item));
            }
            ctx.record_pattern(pat, PatternKind::Tuple { elems: child_ids });
            LhsPattern::Tuple(elements)
        }
        AstPattern::Deref(_)
        | AstPattern::Dot(_, _)
        | AstPattern::Index(_, _, _)
        | AstPattern::Some(_)
        | AstPattern::Missing(_) => {
            // These forms are handled at the AssignLhs layer in `lower_lhs_pattern`.
            unreachable!("unexpected non-binding pattern in lower_lhs_pat")
        }
    }
}

fn lower_assign_pattern(ctx: &mut TyLowerCtx<'_>, pat: &Node<AstPattern>) -> AssignLhs {
    match &pat.value {
        AstPattern::Name(_) | AstPattern::Sequence(_) | AstPattern::Tuple(_) => {
            AssignLhs::Pattern(lower_pattern(ctx, pat))
        }
        AstPattern::Deref(node) => {
            // Get LocalBindingId from resolutions
            let local_id = match ctx.resolutions.get(&pat.id) {
                Some(Resolution::Local(local_id)) => *local_id,
                _ => {
                    log::warn!("Deref pattern {:?} not found in resolutions", pat.id);
                    ctx.record_pattern(pat, PatternKind::Missing);
                    return AssignLhs::ErrorPlaceholder;
                }
            };
            let _binding = ctx.binding_from_node_or_path(pat.id, &node.value.path);
            ctx.record_pattern(pat, PatternKind::Deref { binding: local_id });
            AssignLhs::Deref(local_id)
        }
        AstPattern::Dot(lhs_pat, field_name) => {
            // Only support `x.field = rhs` where `x` is a simple name.
            match &lhs_pat.value {
                AstPattern::Name(n) => {
                    // Get LocalBindingId from resolutions
                    let local_id = match ctx.resolutions.get(&lhs_pat.id) {
                        Some(Resolution::Local(local_id)) => *local_id,
                        _ => {
                            log::warn!(
                                "Field pattern base {:?} not found in resolutions",
                                lhs_pat.id
                            );
                            ctx.record_pattern(pat, PatternKind::Missing);
                            return AssignLhs::ErrorPlaceholder;
                        }
                    };
                    let _binding = ctx.binding_from_node_or_path(lhs_pat.id, &n.path);
                    ctx.record_pattern(lhs_pat, PatternKind::Binding { binding: local_id });
                    let field = field_name
                        .path
                        .name()
                        .unwrap_or_else(|| field_name.to_string());
                    let base_id = ctx.expr_id(lhs_pat);
                    ctx.record_pattern(
                        pat,
                        PatternKind::Field {
                            base: base_id,
                            field: field.clone(),
                        },
                    );
                    AssignLhs::Field {
                        recv: local_id,
                        field,
                    }
                }
                _ => {
                    todo!("lowering for complex field assignment patterns into ExprKind::Assign")
                }
            }
        }
        AstPattern::Index(lhs, index, _) => match &lhs.value {
            AstPattern::Name(n) => {
                // Get LocalBindingId from resolutions
                let local_id = match ctx.resolutions.get(&lhs.id) {
                    Some(Resolution::Local(local_id)) => *local_id,
                    _ => {
                        log::warn!("Index pattern base {:?} not found in resolutions", lhs.id);
                        ctx.record_pattern(pat, PatternKind::Missing);
                        return AssignLhs::ErrorPlaceholder;
                    }
                };
                let _binding = ctx.binding_from_node_or_path(lhs.id, &n.path);
                let lowered_index = lower_expr(ctx, index.as_ref());
                let base_id = ctx.expr_id(lhs.as_ref());
                ctx.record_pattern(lhs.as_ref(), PatternKind::Binding { binding: local_id });
                ctx.record_pattern(
                    pat,
                    PatternKind::Index {
                        container: base_id,
                        index: lowered_index,
                    },
                );
                AssignLhs::Index {
                    container: local_id,
                    index: lowered_index,
                }
            }
            _ => todo!("lowering for complex index assignment patterns into ExprKind::Assign"),
        },
        AstPattern::Some(_) => {
            // Assignment with `some(...)` patterns on the left-hand side is
            // not permitted; these should be rejected earlier in the pipeline
            // (Section A.7 only covers `some(x)` in guard positions).
            unreachable!(
                "assignment with `some(...)` pattern on the left-hand side should be rejected before typing"
            )
        }
        AstPattern::Missing(_) => {
            ctx.record_pattern(pat, PatternKind::Missing);
            // `Missing` is the error placeholder pattern. To keep type
            // checking progressing on partially-invalid ASTs, we treat this
            // like an ignored left-hand side: no bindings are introduced and
            // the assignment constraints only affect the right-hand side and
            // the overall result type.
            AssignLhs::ErrorPlaceholder
        }
    }
}

fn lower_expr(ctx: &mut TyLowerCtx<'_>, node: &Node<Expr>) -> NodeId {
    match &node.value {
        Expr::Assign(assign) => {
            // Assignment expressions `lhs = rhs` (docs/type-system.md A.8).
            //
            // We currently support:
            // - Simple name patterns `x = rhs`.
            // - Deref patterns `*x = rhs` where `x` is a simple name.
            // - Field patterns `x.field = rhs` where `x` is a simple name.
            // - Tuple / sequence destructuring where every element is a
            //   simple name, e.g. `(a, b) = rhs` or `a, b = rhs`.
            //
            // More complex patterns and mutation targets (index, nested
            // destructuring, struct patterns) are left as explicit TODOs
            // so that future work can fill them in.

            let rhs = lower_expr(ctx, &assign.rhs);

            let lhs = lower_assign_pattern(ctx, &assign.lhs);

            let lhs_pattern = ctx.expr_id(&assign.lhs);

            ctx.record_expr(
                node,
                ExprKind::Assign {
                    lhs_pattern,
                    lhs,
                    rhs,
                },
            )
        }
        Expr::BinOp(binop) => {
            let lhs = lower_expr(ctx, &binop.lhs);
            let rhs = lower_expr(ctx, &binop.rhs);
            let op_sym = binop.op.to_string();
            if let Some((method_fqn, trait_fqn)) = ctx.env.infix_op(&op_sym) {
                let result_id = ctx.expr_id(node);
                let args = vec![lhs, rhs];
                let operator_id = ctx.record_expr(
                    &binop.op,
                    ExprKind::OpFunc {
                        trait_name: trait_fqn.to_string(),
                        args,
                        result: result_id,
                    },
                );
                ctx.record_expr(
                    node,
                    ExprKind::BinaryOp {
                        trait_fqn: trait_fqn.clone(),
                        method_fqn: method_fqn.clone(),
                        lhs,
                        rhs,
                        operator: operator_id,
                    },
                )
            } else {
                ctx.emit_error(
                    node,
                    format!(
                        "unsupported binary operator `{}` ({})",
                        op_sym,
                        binop.op.value.as_str()
                    ),
                );
                ctx.record_expr(node, ExprKind::Missing)
            }
        }
        Expr::Block(block) => {
            if block.stmts.is_empty() {
                ctx.record_expr(node, ExprKind::Tuple { elems: Vec::new() })
            } else {
                let mut items = Vec::with_capacity(block.stmts.len());
                for stmt in &block.stmts {
                    items.push(lower_expr(ctx, stmt));
                }
                ctx.record_expr(node, ExprKind::Sequence { items })
            }
        }
        Expr::Boxed(boxed) => {
            let expr = lower_expr(ctx, &boxed.inner);
            ctx.record_expr(node, ExprKind::Boxed { expr })
        }
        Expr::Break(opt_expr) => {
            let expr = opt_expr.as_ref().map(|e| lower_expr(ctx, e));
            ctx.record_expr(node, ExprKind::Break { expr })
        }
        // Function calls.
        Expr::Call(call) => {
            let callee = lower_expr(ctx, &call.callee);
            let mut args = Vec::with_capacity(call.args.items.len());
            for arg in &call.args.items {
                args.push(lower_expr(ctx, arg));
            }
            ctx.record_expr(node, ExprKind::Call { callee, args })
        }
        // Cast expressions `e as T` change the expression's type to the
        // target type (docs/type-system.md A.9).
        //
        // TODO: Thread the cast target type `T` into the v2 IR (for example
        //       by attaching a monomorphic type to `ExprKind::Cast`) so that
        //       constraint generation can see `Tcast'` explicitly and check
        //       its well-formedness.
        Expr::Cast(cast) => {
            let expr = lower_expr(ctx, &cast.lhs);
            let ty = cast.ty.value().clone();
            ctx.record_expr(node, ExprKind::Cast { expr, ty })
        }
        Expr::Closure(closure) => {
            // Anonymous function expression `fn(p1, ..., pn) { body }`.
            //
            // For now we support parameter lists where each parameter is a
            // simple name. The parameters are lowered into LocalBindingIds from
            // the resolutions in a fresh local scope for the closure body.
            ctx.enter_scope();
            let mut params: Vec<LocalBindingId> = Vec::with_capacity(closure.args.items.len());
            for param in &closure.args.items {
                match &param.value {
                    Expr::Name(name) => {
                        // Get LocalBindingId from resolutions
                        let local_id = match ctx.resolutions.get(&param.id) {
                            Some(Resolution::Local(local_id)) => *local_id,
                            _ => {
                                log::warn!("Closure param {:?} not found in resolutions", param.id);
                                continue;
                            }
                        };
                        // Also record in legacy binding system
                        let _binding = ctx.binding_from_node_or_path(param.id, &name.path);
                        params.push(local_id);
                    }
                    _ => {
                        ctx.exit_scope();
                        todo!(
                            "lowering for closure parameters that are not simple names into ExprKind"
                        );
                    }
                }
            }
            let body = lower_expr(ctx, &closure.body);
            ctx.exit_scope();
            ctx.record_expr(node, ExprKind::Closure { params, body })
        }
        // Struct literals `A { x: e1, y: e2 }` (docs/type-system.md 4.5).
        // We require a named struct on the LHS; unlabeled `{ ... }` forms
        // are left for future extension.
        Expr::Curly(curly) => {
            let struct_name = if let Some(lhs) = &curly.lhs {
                lhs.value().to_string()
            } else {
                todo!("lowering for anonymous `{{...}}` curly expressions into ExprKind")
            };

            let mut fields = Vec::with_capacity(curly.elements.len());
            for elem in &curly.elements {
                match &elem.value {
                    CurlyElement::Labeled(name, expr) => {
                        let field_name = name.path.name().unwrap_or_else(|| name.to_string());
                        let field_id = lower_expr(ctx, expr);
                        // Make the CurlyElement node behave like a transparent wrapper
                        // so it gets its own NodeId -> type entry (used by LIR/IDE).
                        ctx.record_expr(elem, ExprKind::Wrapper { expr: field_id });
                        fields.push((field_name, elem.id));
                    }
                    CurlyElement::Name(_) => {
                        // Shorthand `A { x }` initializers are desugared to
                        // labeled form `A { x: x }` in the AST lowering
                        // phase (see ast/lower.rs). We should never see the
                        // `Name` variant here.
                        unreachable!("CurlyElement::Name should have been lowered to Labeled")
                    }
                }
            }

            ctx.record_expr(
                node,
                ExprKind::StructLiteral {
                    struct_name,
                    fields,
                },
            )
        }
        Expr::Dict(dict) => {
            let mut entries = Vec::with_capacity(dict.entries.len());
            for (key, value) in dict.entries.iter() {
                let key_id = lower_expr(ctx, key);
                let value_id = lower_expr(ctx, value);
                entries.push((key_id, value_id));
            }
            ctx.record_expr(node, ExprKind::Dict { entries })
        }
        // Default-value expressions appear primarily in parameter positions.
        // As standalone expressions, we treat `default e` as just `e` for
        // typing purposes, since the value's type is what matters here.
        Expr::DefaultValue(value) => {
            let expr = lower_expr(ctx, value);
            ctx.record_expr(node, ExprKind::Wrapper { expr })
        }
        Expr::Deref(deref) => {
            let expr = lower_expr(ctx, &deref.expr);
            ctx.record_expr(node, ExprKind::Deref { expr })
        }
        // Field access `recv.field` (docs/type-system.md 4.5).
        Expr::Dot(dot) => {
            let recv = lower_expr(ctx, &dot.lhs);
            let field = dot.rhs.path.name().unwrap_or_else(|| dot.rhs.to_string());
            log::debug!("[lower_expr] record field access: {:?}", dot);
            ctx.record_expr(node, ExprKind::FieldAccess { recv, field })
        }
        // For-loops, following docs/type-system.md A.6 "For loops":
        // `for pat in e { body }` lowers to `ExprKind::For` with a simplified
        // pattern representation. For now we support only the key
        // pattern-guard shapes that the type system understands:
        // - simple bindings `x`
        // - `some(x)` patterns
        // - `_` as a wildcard via `Missing`.
        Expr::For(for_loop) => {
            let pattern = lower_guard_pattern(ctx, &for_loop.pat);
            let iter_expr = lower_expr(ctx, &for_loop.expr);
            ctx.enter_loop();
            let body = lower_expr(ctx, &for_loop.body);
            ctx.exit_loop();
            ctx.record_expr(
                node,
                ExprKind::For {
                    pattern,
                    iter_expr,
                    body,
                },
            )
        }
        Expr::Func(_) => todo!("expr::func"),
        Expr::If(ifexpr) => {
            // Detect the pattern-if sugar `if pat = expr { ... }` (with an
            // optional `else { ... }`) before lowering the condition as a
            // regular expression.
            if let Expr::Assign(assign_cond) = &ifexpr.cond.value {
                if is_supported_guard_pattern(&assign_cond.lhs) {
                    let scrutinee = lower_expr(ctx, &assign_cond.rhs);
                    let pattern = lower_guard_pattern(ctx, &assign_cond.lhs);
                    let then_branch = lower_expr(ctx, &ifexpr.then);
                    let else_branch = ifexpr.els.as_ref().map(|els| lower_expr(ctx, els));
                    return ctx.record_expr(
                        node,
                        ExprKind::IfPattern {
                            scrutinee,
                            pattern,
                            then_branch,
                            else_branch,
                        },
                    );
                }
            }

            let cond = lower_expr(ctx, &ifexpr.cond);
            let then_branch = lower_expr(ctx, &ifexpr.then);
            let else_branch = if let Some(els) = &ifexpr.els {
                Some(lower_expr(ctx, els))
            } else {
                None
            };
            ctx.record_expr(
                node,
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                },
            )
        }
        Expr::Index(idx) => {
            let container = lower_expr(ctx, &idx.lhs);
            let index = lower_expr(ctx, &idx.index);
            ctx.record_expr(node, ExprKind::Index { container, index })
        }
        Expr::Labeled(_, inner) => {
            let expr = lower_expr(ctx, inner);
            ctx.record_expr(node, ExprKind::Wrapper { expr })
        }
        Expr::List(list) => {
            let mut items = Vec::with_capacity(list.items.len());
            for item in &list.items {
                items.push(lower_expr(ctx, item));
            }
            ctx.record_expr(node, ExprKind::List { items })
        }
        Expr::Literal(lit) => lower_literal(ctx, node, lit),
        Expr::Loop(loop_expr) => {
            ctx.enter_loop();
            let body = lower_expr(ctx, &loop_expr.body);
            ctx.exit_loop();
            ctx.record_expr(node, ExprKind::Loop { body })
        }
        Expr::Missing(_) => {
            // Parsed placeholder expression; we lower this to an unconstrained
            // missing node so that the rest of the tree can still be typed.
            ctx.record_expr(node, ExprKind::Missing)
        }
        // Variable references: use the resolutions table to determine whether
        // this is a local binding or a top-level definition reference.
        Expr::Name(_) => {
            if let Some(resolution) = ctx.resolutions.get(&node.id) {
                match resolution {
                    Resolution::Local(local_id) => {
                        ctx.record_expr(node, ExprKind::LocalRef(*local_id))
                    }
                    Resolution::Def(DefTarget::Workspace(def_id)) => {
                        ctx.record_expr(node, ExprKind::DefRef(*def_id))
                    }
                    Resolution::Def(DefTarget::Library(_)) => {
                        // External references (from libraries) - emit Missing for now
                        // TODO: Handle library references properly once we have DefId for externals
                        ctx.record_expr(node, ExprKind::Missing)
                    }
                    Resolution::Error => ctx.record_expr(node, ExprKind::Missing),
                }
            } else {
                ctx.emit_error(node, "unresolved name reference".to_string());
                ctx.record_expr(node, ExprKind::Missing)
            }
        }
        Expr::New(new) => {
            // Heap allocation `new(T, count?)`. The element type `T` comes
            // from the parsed type annotation on the expression and is not
            // yet threaded into this IR; we only lower the optional `count`
            // expression so it participates in type checking.
            let count = new.count.as_ref().map(|c| lower_expr(ctx, c));
            ctx.record_expr(node, ExprKind::New { count })
        }
        Expr::Paren(inner) => {
            let expr = lower_expr(ctx, inner);
            ctx.record_expr(node, ExprKind::Wrapper { expr })
        }
        Expr::Path(_) => {
            // Path expressions use the same resolution mechanism as Name expressions
            if let Some(resolution) = ctx.resolutions.get(&node.id) {
                match resolution {
                    Resolution::Local(local_id) => {
                        ctx.record_expr(node, ExprKind::LocalRef(*local_id))
                    }
                    Resolution::Def(DefTarget::Workspace(def_id)) => {
                        ctx.record_expr(node, ExprKind::DefRef(*def_id))
                    }
                    Resolution::Def(DefTarget::Library(_)) => {
                        // External references (from libraries)
                        // TODO: Handle library references properly
                        ctx.record_expr(node, ExprKind::Missing)
                    }
                    Resolution::Error => ctx.record_expr(node, ExprKind::Missing),
                }
            } else {
                ctx.emit_error(node, "unresolved path reference".to_string());
                ctx.record_expr(node, ExprKind::Missing)
            }
        }
        Expr::Pattern(pattern) => {
            // Pattern-as-expression nodes are sugar for the corresponding
            // expression form (Name, Tuple, Dot, Some, etc.). Convert the
            // pattern back into an Expr and reuse the regular expression
            // lowering rules so that we get a proper ExprKind and source.
            let desugared: Expr = pattern.clone().into();
            let synthetic = Node::with_id(node.id, desugared);
            lower_expr(ctx, &synthetic)
        }
        Expr::Range(range) => {
            // Range expressions `start .. end` / `start ..= end`.
            //
            // The front-end library defines a nominal `range['a]` struct
            // (lib/core/range.ray). For typing we treat `start .. end`
            // as producing a `range[T]` where `T` is the element type of
            // the `start`/`end` expressions, and we do not currently
            // surface the `inclusive` flag in the type.
            let start = lower_expr(ctx, &range.start);
            let end = lower_expr(ctx, &range.end);
            ctx.record_expr(
                node,
                ExprKind::Range {
                    start,
                    end,
                    inclusive: matches!(range.limits, RangeLimits::Inclusive),
                },
            )
        }
        Expr::Ref(rf) => {
            let expr = lower_expr(ctx, &rf.expr);
            ctx.record_expr(node, ExprKind::Ref { expr })
        }
        Expr::Return(opt_expr) => {
            // If this is `return e`, lower the inner expression and attach it.
            // If this is a bare `return`, we use the return expression node
            // itself as the payload; it will receive a fresh meta type that
            // is equated with the current function result type by the
            // constraint generator (docs/type-system.md A.6 "Return
            // expressions").
            let expr = opt_expr.as_ref().map(|expr| lower_expr(ctx, expr));
            ctx.record_expr(node, ExprKind::Return { expr })
        }
        Expr::Continue => {
            if ctx.loop_depth == 0 {
                ctx.emit_error(node, "`continue` is only valid inside a loop");
            }
            ctx.record_expr(node, ExprKind::Continue)
        }
        Expr::Sequence(seq) => {
            let mut elems = Vec::with_capacity(seq.items.len());
            for item in &seq.items {
                elems.push(lower_expr(ctx, item));
            }
            ctx.record_expr(node, ExprKind::Tuple { elems })
        }
        Expr::Set(set) => {
            let mut items = Vec::with_capacity(set.items.len());
            for item in set.items.iter() {
                items.push(lower_expr(ctx, item));
            }
            ctx.record_expr(node, ExprKind::Set { items })
        }
        Expr::ScopedAccess(scoped_access) => {
            // For now we support `type[T]::name` style access only when the LHS is
            // an explicit type expression (e.g. `dict['k, 'v]::with_capacity`),
            // lowering it to a fully-qualified value path `T::name`.
            if let Expr::Type(ty) = &scoped_access.lhs.value {
                let member_name = scoped_access
                    .rhs
                    .value
                    .path
                    .name()
                    .unwrap_or_else(|| scoped_access.rhs.value.to_string());

                // Use the resolutions table to find the target definition
                if let Some(resolution) = ctx.resolutions.get(&node.id) {
                    match resolution {
                        Resolution::Def(DefTarget::Workspace(def_id)) => ctx.record_expr(
                            node,
                            ExprKind::ScopedAccess {
                                def_id: *def_id,
                                member_name,
                                lhs_ty: ty.value().mono().clone(),
                            },
                        ),
                        _ => {
                            ctx.emit_error(
                                node,
                                "scoped access must resolve to a definition".to_string(),
                            );
                            ctx.record_expr(node, ExprKind::Missing)
                        }
                    }
                } else {
                    ctx.emit_error(node, "could not resolve scoped access".to_string());
                    ctx.record_expr(node, ExprKind::Missing)
                }
            } else {
                ctx.emit_error(
                    node,
                    format!(
                        "expected a type on the left-hand side of `::`, but found `{}`",
                        scoped_access.lhs.value
                    ),
                );
                ctx.record_expr(node, ExprKind::Missing)
            }
        }
        // Optional / nil expressions map onto the nilable forms.
        Expr::Some(inner) => {
            let expr = lower_expr(ctx, inner);
            ctx.record_expr(node, ExprKind::Some { expr })
        }
        Expr::Tuple(tuple) => {
            let mut elems = Vec::with_capacity(tuple.seq.items.len());
            for item in &tuple.seq.items {
                elems.push(lower_expr(ctx, item));
            }
            ctx.record_expr(node, ExprKind::Tuple { elems })
        }
        Expr::Type(ty) => {
            let ty = ty.value().mono().clone();
            ctx.record_expr(node, ExprKind::Type { ty })
        }
        Expr::TypeAnnotated(value, _) => {
            let expr = lower_expr(ctx, value);
            ctx.record_expr(node, ExprKind::Wrapper { expr })
        }
        Expr::UnaryOp(unary) => {
            let expr = lower_expr(ctx, &unary.expr);
            let op_sym = unary.op.to_string();
            if let Some((method_fqn, trait_fqn)) = ctx.env.prefix_op(&op_sym) {
                let result_id = ctx.expr_id(node);
                let operator_id = ctx.record_expr(
                    &unary.op,
                    ExprKind::OpFunc {
                        trait_name: trait_fqn.to_string(),
                        args: vec![expr],
                        result: result_id,
                    },
                );
                ctx.record_expr(
                    node,
                    ExprKind::UnaryOp {
                        trait_fqn: trait_fqn.clone(),
                        method_fqn: method_fqn.clone(),
                        operator: operator_id,
                        expr,
                    },
                )
            } else {
                ctx.emit_error(
                    node,
                    format!(
                        "unsupported unary operator `{}`; missing trait implementation",
                        op_sym
                    ),
                );
                ctx.record_expr(node, ExprKind::Missing)
            }
        }
        Expr::Unsafe(inner) => lower_expr(ctx, inner),
        Expr::While(whileexpr) => {
            let cond = lower_expr(ctx, &whileexpr.cond);
            ctx.enter_loop();
            let body = lower_expr(ctx, &whileexpr.body);
            ctx.exit_loop();
            ctx.record_expr(node, ExprKind::While { cond, body })
        }
    }
}

fn lower_literal(ctx: &mut TyLowerCtx<'_>, node: &Node<Expr>, lit: &Literal) -> NodeId {
    let kind = match lit {
        Literal::Bool(b) => ExprKind::LiteralBool(*b),
        Literal::Integer { size, signed, .. } => {
            if let Some(size) = size {
                let sign = if !signed { "u" } else { "i" };
                let ty = if *size != 0 {
                    format!("{}{}", sign, size)
                } else {
                    format!("{}int", sign)
                };
                ExprKind::LiteralIntSized(Ty::con(ty.as_str()))
            } else {
                ExprKind::LiteralInt
            }
        }
        Literal::Float { size, .. } => {
            if *size != 0 {
                ExprKind::LiteralFloatSized
            } else {
                ExprKind::LiteralFloat
            }
        }
        Literal::Nil => ExprKind::Nil,
        Literal::String(_) => ExprKind::LiteralString,
        Literal::ByteString(_) => ExprKind::LiteralByteString,
        Literal::Byte(_) => ExprKind::LiteralByte,
        Literal::Char(_) => ExprKind::LiteralChar,
        Literal::UnicodeEscSeq(_) => ExprKind::LiteralUnicodeEsc,
        Literal::Unit => {
            // Treat `()` as the unit expression, which we model as an
            // empty tuple type in the core type system.
            ExprKind::Tuple { elems: Vec::new() }
        }
    };

    ctx.record_expr(node, kind)
}

/// Lower an `ast::Pattern` appearing in a guard position (`for` pattern,
/// future pattern-if/while) into the simplified `Pattern` used by the
/// constraint generator. This focuses on the shapes relevant to
/// docs/type-system.md A.6:
/// - plain bindings `x`
/// - `some(x)` patterns
/// - a wildcard `_` (represented here via `Missing`).
fn lower_guard_pattern(ctx: &mut TyLowerCtx<'_>, pat: &Node<AstPattern>) -> Pattern {
    match &pat.value {
        AstPattern::Name(name) => {
            // Get LocalBindingId from resolutions
            let local_id = match ctx.resolutions.get(&pat.id) {
                Some(Resolution::Local(local_id)) => *local_id,
                _ => {
                    log::warn!("Guard pattern {:?} not found in resolutions", pat.id);
                    return Pattern::Wild;
                }
            };
            let _binding = ctx.binding_from_node_or_path(pat.id, &name.path);
            Pattern::Binding(local_id)
        }
        AstPattern::Some(inner) => match &inner.value {
            AstPattern::Name(name) => {
                // Get LocalBindingId from resolutions
                let local_id = match ctx.resolutions.get(&inner.id) {
                    Some(Resolution::Local(local_id)) => *local_id,
                    _ => {
                        log::warn!("Some pattern inner {:?} not found in resolutions", inner.id);
                        return Pattern::Wild;
                    }
                };
                let _binding = ctx.binding_from_node_or_path(inner.id, &name.path);
                Pattern::Some(local_id)
            }
            _ => {
                todo!("lowering for complex `some(...)` patterns into Pattern")
            }
        },
        AstPattern::Missing(_) => {
            // Treat the "missing" placeholder pattern as a wildcard.
            Pattern::Wild
        }
        _ => {
            todo!(
                "lowering for complex pattern `{:?}` into Pattern",
                pat.value
            )
        }
    }
}

fn is_supported_guard_pattern(pat: &Node<AstPattern>) -> bool {
    match &pat.value {
        AstPattern::Name(_) => true,
        AstPattern::Some(inner) => matches!(inner.value, AstPattern::Name(_)),
        AstPattern::Missing(_) => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, rc::Rc};

    use ray_shared::{
        collections::namecontext::NameContext,
        def::DefId,
        file_id::FileId,
        node_id::{NodeId, NodeIdGuard},
        pathlib::{FilePath, Path as RayPath},
        resolution::Resolution,
        span::{Source as RaySource, Span},
    };
    use ray_typing::{
        TypecheckOptions, context::ExprKind, env::GlobalEnv, mocks::MockTypecheckEnv, tyctx::TyCtx,
    };

    use crate::{
        ast::{Block, Boxed, Decl, Expr, Func, Literal, Module, Node},
        passes::{FrontendPassManager, deps::build_binding_graph},
        sourcemap::SourceMap,
        typing::{build_def_binding_records, build_typecheck_input, collect_def_ids},
    };

    /// Set up a DefId context for tests that create nodes.
    fn test_def_context() -> NodeIdGuard {
        NodeId::enter_def(DefId::new(FileId(0), 0))
    }

    fn make_test_source() -> RaySource {
        RaySource::new(
            FilePath::from("test.ray"),
            Span::new(),
            RayPath::new(),
            RayPath::new(),
        )
    }

    #[test]
    fn lower_simple_bool_function_into_module_input() {
        let _guard = test_def_context();
        // Build a minimal module with a single function:
        //
        //   fn f() { true }
        //
        // and ensure it lowers into a ModuleInput with:
        // - one BindingId for `f`
        // - a root expression of kind LiteralBool(true).

        // Function path `f`
        let func_path = Node::new(RayPath::from("f"));
        let func_body_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let func_body_block = Node::new(Expr::Block(Block {
            stmts: vec![func_body_expr.clone()],
        }));
        let func = Func::new(func_path, vec![], func_body_block);
        let func_decl = Node::new(Decl::Func(func));

        let module: Module<(), Decl> = Module {
            path: RayPath::from("test"),
            stmts: vec![],
            decls: vec![func_decl],
            imports: vec![],
            import_stmts: vec![],
            submodules: vec![],
            doc_comment: None,
            root_filepath: FilePath::from("test.ray"),
            filepaths: vec![FilePath::from("test.ray")],
            is_lib: false,
        };

        let mut srcmap = SourceMap::new();
        srcmap.set_src(&func_body_expr, make_test_source());

        let env = GlobalEnv::new();
        let mut tcx = TyCtx::new(env);
        let resolutions: HashMap<NodeId, Resolution> = HashMap::new();
        let typecheck_env = MockTypecheckEnv::new();
        let mut pass_manager = FrontendPassManager::new(&module, &srcmap, &mut tcx, &resolutions);
        let binding_output = pass_manager.binding_output().clone();
        let def_ids = collect_def_ids(&module);
        let def_bindings = build_binding_graph(&def_ids, &resolutions);
        let def_binding_records = build_def_binding_records(&binding_output);
        let input = build_typecheck_input(
            &module.decls,
            &[],
            &srcmap,
            &typecheck_env,
            &binding_output,
            &resolutions,
            def_bindings,
            def_binding_records,
            Rc::default(),
        );

        // There should be exactly one binding record with a body expression.
        assert_eq!(input.binding_records.len(), 1);
        let (&binding_id, record) = input.binding_records.iter().next().unwrap();
        let root_expr = record.body_expr.expect("binding should have body expr");

        // The binding graph should know about this binding.
        assert!(input.bindings.edges.contains_key(&binding_id));

        // The root expression should be a zero-arg function whose body is the bool literal.
        let kind = input.expr_kind(root_expr).unwrap();
        match kind {
            ExprKind::Function { params, body } => {
                assert!(params.is_empty(), "expected zero params");
                let body_kind = input.expr_kind(*body).unwrap();
                match body_kind {
                    ExprKind::Sequence { items } => {
                        assert_eq!(items.len(), 1, "expected single statement in block");
                        let lit_kind = input.expr_kind(items[0]).unwrap();
                        match lit_kind {
                            ExprKind::LiteralBool(true) => {}
                            other => panic!("expected LiteralBool(true), got {:?}", other),
                        }
                    }
                    other => panic!("expected sequence block, got {:?}", other),
                }
            }
            other => panic!("expected function wrapper, got {:?}", other),
        }
    }

    #[test]
    fn typecheck_simple_bool_function_with_new_typechecker() {
        let _guard = test_def_context();

        let func_path = Node::new(RayPath::from("g"));
        let func_body_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let func_body_block = Node::new(Expr::Block(Block {
            stmts: vec![func_body_expr.clone()],
        }));
        let func = Func::new(func_path, vec![], func_body_block);
        let func_decl = Node::new(Decl::Func(func));

        let module: Module<(), Decl> = Module {
            path: RayPath::from("test2"),
            stmts: vec![],
            decls: vec![func_decl],
            imports: vec![],
            import_stmts: vec![],
            submodules: vec![],
            doc_comment: None,
            root_filepath: FilePath::from("test2.ray"),
            filepaths: vec![FilePath::from("test2.ray")],
            is_lib: false,
        };

        let mut srcmap = SourceMap::new();
        srcmap.set_src(&func_body_expr, make_test_source());

        let global_env = GlobalEnv::new();
        let mut tcx = TyCtx::new(global_env);
        let ncx = NameContext::new();
        let options = TypecheckOptions::default();
        let resolutions: HashMap<NodeId, Resolution> = HashMap::new();
        let mut pass_manager = FrontendPassManager::new(&module, &srcmap, &mut tcx, &resolutions);
        let result = pass_manager.typecheck(&ncx, options).clone();

        assert!(
            result.errors.is_empty(),
            "expected no type errors, got {:?}",
            result.errors
        );
    }

    #[test]
    fn typecheck_boxed_bool_function_with_new_typechecker() {
        let _guard = test_def_context();
        // fn b() { box true }
        //
        // This exercises lowering of Boxed and the Boxed => *T rule in the
        // constraint generator.

        let func_path = Node::new(RayPath::from("b"));

        let inner_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let boxed_expr = Node::new(Expr::Boxed(Boxed {
            inner: Box::new(inner_expr.clone()),
            box_span: Span::new(),
        }));

        let func_body_block = Node::new(Expr::Block(Block {
            stmts: vec![boxed_expr.clone()],
        }));
        let func = Func::new(func_path, vec![], func_body_block);
        let func_decl = Node::new(Decl::Func(func));

        let module: Module<(), Decl> = Module {
            path: RayPath::from("test_boxed"),
            stmts: vec![],
            decls: vec![func_decl],
            imports: vec![],
            import_stmts: vec![],
            submodules: vec![],
            doc_comment: None,
            root_filepath: FilePath::from("test_boxed.ray"),
            filepaths: vec![FilePath::from("test_boxed.ray")],
            is_lib: false,
        };

        let mut srcmap = SourceMap::new();
        srcmap.set_src(&boxed_expr, make_test_source());

        let global_env = GlobalEnv::new();
        let mut tcx = TyCtx::new(global_env);
        let ncx = NameContext::new();
        let options = TypecheckOptions::default();
        let resolutions: HashMap<NodeId, Resolution> = HashMap::new();
        let mut pass_manager = FrontendPassManager::new(&module, &srcmap, &mut tcx, &resolutions);
        let result = pass_manager.typecheck(&ncx, options).clone();

        assert!(
            result.errors.is_empty(),
            "expected no type errors for boxed bool, got {:?}",
            result.errors
        );
    }
}

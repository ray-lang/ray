use std::collections::HashMap;

use ray_shared::{
    def::DefId,
    file_id::FileId,
    local_binding::LocalBindingId,
    node_id::NodeId,
    pathlib::ItemPath,
    resolution::{DefTarget, Resolution},
    ty::Ty,
};
use ray_typing::{
    ExprRecord, PatternKind, PatternRecord, TypeCheckInput, TypeError,
    binding_groups::BindingGraph,
    context::{AssignLhs, BuiltinOp, ExprKind, LhsPattern, Pattern},
    env::TypecheckEnv,
    info::TypeSystemInfo,
};

use crate::{
    ast::{
        BuiltinKind, CurlyElement, Decl, Expr, FStringPart, Literal, Node, Pattern as AstPattern,
        RangeLimits,
    },
    sourcemap::SourceMap,
};

struct TyLowerCtx<'a> {
    srcmap: &'a SourceMap,
    env: &'a dyn TypecheckEnv,
    resolutions: &'a HashMap<NodeId, Resolution>,
    expr_records: HashMap<NodeId, ExprRecord>,
    pattern_records: HashMap<NodeId, PatternRecord>,
    /// Mapping from DefId to the root expression NodeId for each definition.
    /// This is used by the typechecker to find the body expression for a binding.
    def_nodes: HashMap<DefId, NodeId>,
    /// Top-level statements for each file's FileMain (DefId with index 0).
    /// Unlike other bindings, FileMain doesn't have a single root expression.
    file_main_stmts: HashMap<DefId, Vec<NodeId>>,
    loop_depth: usize,
    errors: Vec<TypeError>,
}

impl<'a> TyLowerCtx<'a> {
    fn new(
        srcmap: &'a SourceMap,
        env: &'a dyn TypecheckEnv,
        resolutions: &'a HashMap<NodeId, Resolution>,
    ) -> Self {
        TyLowerCtx {
            srcmap,
            env,
            resolutions,
            expr_records: HashMap::new(),
            pattern_records: HashMap::new(),
            def_nodes: HashMap::new(),
            file_main_stmts: HashMap::new(),
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

    fn enter_loop(&mut self) {
        self.loop_depth += 1;
    }

    fn exit_loop(&mut self) {
        self.loop_depth = self.loop_depth.saturating_sub(1);
    }

    fn emit_error<T>(&mut self, node: &Node<T>, msg: impl Into<String>) {
        self.emit_error_at(node.id, msg);
    }

    fn emit_error_at(&mut self, node_id: NodeId, msg: impl Into<String>) {
        let mut info = TypeSystemInfo::new();
        if let Some(src) = self.srcmap.get_by_id(node_id) {
            info.with_src(src);
        }
        self.errors.push(TypeError::message(msg, info));
    }
}

pub fn build_typecheck_input(
    decls: &[Node<Decl>],
    top_level_stmts: &[Node<Expr>],
    srcmap: &SourceMap,
    env: &dyn TypecheckEnv,
    resolutions: &HashMap<NodeId, Resolution>,
    def_bindings: BindingGraph<DefId>,
) -> TypeCheckInput {
    let mut ctx = TyLowerCtx::new(srcmap, env, resolutions);

    // Lower top-level statements as the body of FileMain (DefId with index 0).
    // FileMain owns all top-level statements and any LocalBindingIds they create.
    if !top_level_stmts.is_empty() {
        lower_file_main(&mut ctx, top_level_stmts);
    }

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
                    for decl_node in funcs {
                        let Decl::Func(func) = &decl_node.value else {
                            unreachable!("impl funcs should only contain Decl::Func");
                        };
                        if let Some(body) = &func.body {
                            lower_func_binding(&mut ctx, decl_node.id, &func.sig, body);
                        }
                    }
                }

                // Consts inside the impl.
                if let Some(consts) = &im.consts {
                    for assign_node in consts {
                        match &assign_node.lhs.value {
                            AstPattern::Name(_) => {
                                let _root_expr_id = lower_expr(&mut ctx, &assign_node.rhs);
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
                        let _root_expr_id = lower_expr(&mut ctx, &assign.rhs);
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
            // Extern declarations don't have bodies to lower - their types come
            // from the environment via external_scheme().
            Decl::Mutable(_, _) | Decl::Name(_, _) => {
                // TODO: lower declaration-only bindings into value bindings
                // once their typing rules are specified.
            }
            Decl::FileMain(stmts) => {
                // FileMain statements are lowered via the top_level_stmts parameter,
                // not via the decls iteration. But we now wrap them in a Decl::FileMain
                // node, so we can handle them here directly.
                if !stmts.is_empty() {
                    lower_file_main(&mut ctx, stmts);
                }
            }
            Decl::Test(test) => {
                // Test blocks are lowered like FileMain: their body statements
                // are registered in file_main_stmts so the typechecker processes
                // each statement and infers types for all expressions.
                if let Expr::Block(block) = &test.body.value {
                    if !block.stmts.is_empty() {
                        let test_def = decl_node.id.owner;
                        let mut stmt_ids = Vec::with_capacity(block.stmts.len());
                        for stmt in &block.stmts {
                            let stmt_id = lower_expr(&mut ctx, stmt);
                            stmt_ids.push(stmt_id);
                        }
                        ctx.file_main_stmts.insert(test_def, stmt_ids);
                    }
                }
            }
        }
    }

    TypeCheckInput {
        bindings: def_bindings,
        def_nodes: ctx.def_nodes,
        file_main_stmts: ctx.file_main_stmts,
        expr_records: ctx.expr_records,
        pattern_records: ctx.pattern_records,
        lowering_errors: ctx.errors,
    }
}

/// Lower top-level statements as the body of FileMain.
///
/// FileMain is `DefId { file, index: 0 }` - the top-level execution context for
/// each file. All top-level statements are owned by FileMain and their NodeIds
/// have `owner` pointing to FileMain's DefId.
///
/// Unlike regular bindings which have a single root expression, FileMain has
/// multiple statements that are stored separately in `file_main_stmts`.
fn lower_file_main(ctx: &mut TyLowerCtx<'_>, stmts: &[Node<Expr>]) {
    // Get the FileMain DefId from the first statement's owner.
    // All top-level statements should have the same owner (FileMain).
    let file_main_def = stmts[0].id.owner;
    debug_assert!(
        file_main_def.index == 0,
        "FileMain should have index 0, got {}",
        file_main_def.index
    );

    // Lower each statement and collect their NodeIds.
    let mut stmt_ids = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        let stmt_id = lower_expr(ctx, stmt);
        stmt_ids.push(stmt_id);
    }

    // Store the statements for FileMain - the typechecker handles FileMain specially.
    ctx.file_main_stmts.insert(file_main_def, stmt_ids);
}

fn lower_func_binding(
    ctx: &mut TyLowerCtx<'_>,
    decl_id: NodeId,
    sig: &crate::ast::FuncSig,
    body: &Node<Expr>,
) {
    let mut param_bindings: Vec<LocalBindingId> = Vec::with_capacity(sig.params.len());

    // Each function body gets its own local scope for bindings introduced
    // by parameters, assignments, and other local-binding forms.
    for param_node in &sig.params {
        // Get LocalBindingId from resolutions (set by name resolution phase)
        let local_id = match ctx.resolutions.get(&param_node.id) {
            Some(Resolution::Local(local_id)) => *local_id,
            _ => {
                // Fallback: create a placeholder LocalBindingId if not resolved
                log::debug!("Parameter {:?} not found in resolutions", param_node.id);
                continue;
            }
        };
        param_bindings.push(local_id);
        // Record the parameter in pattern_records so it can be looked up later
        // (e.g., by local_binding_for_node during LIR generation)
        ctx.record_pattern(param_node, PatternKind::Binding { binding: local_id });
    }
    let body_expr_id = lower_expr(ctx, body);

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

    // Record the mapping from DefId to root expression NodeId
    ctx.def_nodes.insert(decl_id.owner, decl_id);
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
        AstPattern::Name(_) => {
            // Get LocalBindingId from resolutions
            let local_id = match ctx.resolutions.get(&pat.id) {
                Some(Resolution::Local(local_id)) => *local_id,
                _ => {
                    // Fallback for unresolved patterns - should not happen in valid code
                    log::debug!("Pattern {:?} not found in resolutions", pat.id);
                    ctx.record_pattern(pat, PatternKind::Missing);
                    return LhsPattern::Binding(LocalBindingId::new(DefId::new(FileId(0), 0), 0));
                }
            };
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
        AstPattern::Deref(inner_name) => {
            // Get LocalBindingId from resolutions.
            // Name resolution records at the inner name's NodeId (via paths_mut()),
            // not the deref pattern's NodeId.
            let local_id = match ctx.resolutions.get(&inner_name.id) {
                Some(Resolution::Local(local_id)) => *local_id,
                _ => {
                    log::debug!(
                        "Deref pattern inner name {:?} not found in resolutions",
                        inner_name.id
                    );
                    ctx.record_pattern(pat, PatternKind::Missing);
                    return AssignLhs::ErrorPlaceholder;
                }
            };
            ctx.record_pattern(pat, PatternKind::Deref { binding: local_id });
            AssignLhs::Deref(local_id)
        }
        AstPattern::Dot(lhs_pat, field_name) => {
            // Only support `x.field = rhs` where `x` is a simple name.
            match &lhs_pat.value {
                AstPattern::Name(_) => {
                    // Get LocalBindingId from resolutions
                    let local_id = match ctx.resolutions.get(&lhs_pat.id) {
                        Some(Resolution::Local(local_id)) => *local_id,
                        _ => {
                            log::debug!(
                                "Field pattern base {:?} not found in resolutions",
                                lhs_pat.id
                            );
                            ctx.record_pattern(pat, PatternKind::Missing);
                            return AssignLhs::ErrorPlaceholder;
                        }
                    };
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
        AstPattern::Index(lhs, index, _) => {
            let lowered_index = lower_expr(ctx, index.as_ref());
            let container_id = ctx.expr_id(lhs.as_ref());

            // Only simple index patterns are supported: l[0] = v where l is a name.
            // Nested index patterns like m[0][1] = v are not supported because
            // Index::get returns a nilable type, and we don't have nilable chaining.
            let AstPattern::Name(_) = &lhs.value else {
                ctx.emit_error(
                    pat,
                    "nested index assignment is not supported; Index::get returns a nilable type",
                );
                ctx.record_pattern(pat, PatternKind::Missing);
                return AssignLhs::ErrorPlaceholder;
            };

            let local_id = match ctx.resolutions.get(&lhs.id) {
                Some(Resolution::Local(local_id)) => *local_id,
                _ => {
                    log::debug!("Index pattern base {:?} not found in resolutions", lhs.id);
                    ctx.record_pattern(pat, PatternKind::Missing);
                    return AssignLhs::ErrorPlaceholder;
                }
            };
            ctx.record_pattern(lhs.as_ref(), PatternKind::Binding { binding: local_id });
            // Also record an expression for the container so it gets typed.
            // The container_id needs a type for constraint generation.
            ctx.expr_records.insert(
                container_id,
                ExprRecord {
                    kind: ExprKind::LocalRef(local_id),
                    source: ctx.srcmap.get_by_id(lhs.id),
                },
            );

            ctx.record_pattern(
                pat,
                PatternKind::Index {
                    container: container_id,
                    index: lowered_index,
                },
            );
            AssignLhs::Index {
                container: container_id,
                index: lowered_index,
            }
        }
        AstPattern::Some(_) => {
            // Assignment with `some(...)` patterns on the left-hand side is
            // not permitted; these should be rejected earlier in the pipeline
            // (Section A.7 only covers `some(x)` in guard positions).
            log::debug!(
                "assignment with `some(...)` pattern on the left-hand side should be rejected before typing"
            );
            ctx.record_pattern(pat, PatternKind::Missing);
            AssignLhs::ErrorPlaceholder
        }
        AstPattern::Missing(_) => {
            // `Missing` is the error placeholder pattern. To keep type
            // checking progressing on partially-invalid ASTs, we treat this
            // like an ignored left-hand side: no bindings are introduced and
            // the assignment constraints only affect the right-hand side and
            // the overall result type.
            ctx.record_pattern(pat, PatternKind::Missing);
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
            if let Some((trait_fqn, method_fqn)) = ctx.env.infix_op(&op_sym) {
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
        Expr::NilCoalesce(nc) => {
            let lhs = lower_expr(ctx, &nc.lhs);
            let rhs = lower_expr(ctx, &nc.rhs);
            ctx.record_expr(node, ExprKind::NilCoalesce { lhs, rhs })
        }
        Expr::FString(fstr) => {
            let parts = fstr
                .parts
                .iter()
                .filter_map(|part| match part {
                    FStringPart::Literal(_) => None,
                    FStringPart::Expr(expr) => Some(lower_expr(ctx, expr)),
                })
                .collect();
            ctx.record_expr(node, ExprKind::FString { parts })
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
            let ty = cast
                .ty
                .root_id()
                .and_then(|id| ctx.env.resolved_expr_ty(id))
                .unwrap_or_else(|| cast.ty.value().clone());
            ctx.record_expr(node, ExprKind::Cast { expr, ty })
        }
        Expr::Closure(closure) => {
            // Anonymous function expression `fn(p1, ..., pn) { body }`.
            //
            // For now we support parameter lists where each parameter is a
            // simple name. The parameters are lowered into LocalBindingIds from
            // the resolutions.
            let mut params: Vec<LocalBindingId> = Vec::with_capacity(closure.args.items.len());
            for param in &closure.args.items {
                match &param.value {
                    Expr::Name(_) => {
                        // Get LocalBindingId from resolutions
                        let local_id = match ctx.resolutions.get(&param.id) {
                            Some(Resolution::Local(local_id)) => *local_id,
                            _ => {
                                log::debug!(
                                    "Closure param {:?} not found in resolutions",
                                    param.id
                                );
                                continue;
                            }
                        };
                        params.push(local_id);
                    }
                    _ => {
                        todo!(
                            "lowering for closure parameters that are not simple names into ExprKind"
                        );
                    }
                }
            }
            let body = lower_expr(ctx, &closure.body);
            ctx.record_expr(node, ExprKind::Closure { params, body })
        }
        // Struct literals `A { x: e1, y: e2 }` (docs/type-system.md 4.5).
        // We require a named struct on the LHS; unlabeled `{ ... }` forms
        // are left for future extension.
        Expr::Curly(curly) => {
            // Get the raw AST path as a fallback
            let ast_path = curly.lhs.as_ref().map(|lhs| ItemPath::from(&lhs.value));

            // Try to get the fully qualified path from name resolution.
            // The resolution was stored by nameresolve.rs for curly expressions.
            let path = match ctx.resolutions.get(&node.id) {
                Some(Resolution::Def(target)) => {
                    // Use the resolved DefTarget to get the fully qualified ItemPath
                    ctx.env.def_item_path(target).or(ast_path)
                }
                _ => ast_path,
            };

            let path = match path {
                Some(p) => p,
                None => {
                    todo!("lowering for anonymous `{{...}}` curly expressions into ExprKind")
                }
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

            ctx.record_expr(node, ExprKind::StructLiteral { path, fields })
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
                    Resolution::Def(target @ DefTarget::Workspace(_))
                    | Resolution::Def(target @ DefTarget::Library(_)) => {
                        ctx.record_expr(node, ExprKind::DefRef(target.clone()))
                    }
                    Resolution::Def(DefTarget::Primitive(_))
                    | Resolution::Def(DefTarget::Module(_)) => {
                        // Primitive type names (int, bool, etc.) used as values
                        ctx.emit_error(node, "type name cannot be used as a value".to_string());
                        ctx.record_expr(node, ExprKind::Missing)
                    }
                    Resolution::TypeParam(_) => {
                        todo!("FIXME: name resolved to type param reference")
                    }
                    Resolution::Error { .. } => ctx.record_expr(node, ExprKind::Missing),
                }
            } else {
                ctx.emit_error(node, "unresolved name reference".to_string());
                ctx.record_expr(node, ExprKind::Missing)
            }
        }
        Expr::New(_) => {
            // Heap allocation `new(T)`. The element type `T` comes from the
            // parsed type annotation on the expression and is not yet
            // threaded into this IR.
            ctx.record_expr(node, ExprKind::New)
        }
        Expr::BuiltinCall(bc) => {
            let arg = lower_expr(ctx, &bc.arg);
            let op = match bc.kind {
                BuiltinKind::Freeze => BuiltinOp::Freeze,
                BuiltinKind::Id => BuiltinOp::Id,
                BuiltinKind::Upgrade => BuiltinOp::Upgrade,
            };
            ctx.record_expr(node, ExprKind::BuiltinCall { op, arg })
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
                    Resolution::Def(target @ DefTarget::Workspace(_))
                    | Resolution::Def(target @ DefTarget::Library(_)) => {
                        ctx.record_expr(node, ExprKind::DefRef(target.clone()))
                    }
                    Resolution::Def(DefTarget::Primitive(_))
                    | Resolution::Def(DefTarget::Module(_)) => {
                        // Primitive type names (int, bool, etc.) used as values
                        ctx.emit_error(node, "type name cannot be used as a value".to_string());
                        ctx.record_expr(node, ExprKind::Missing)
                    }
                    Resolution::TypeParam(_) => {
                        todo!("FIXME: path resolved to type parameter reference")
                    }
                    Resolution::Error { .. } => ctx.record_expr(node, ExprKind::Missing),
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
            let mutable = rf.mutable;
            ctx.record_expr(node, ExprKind::Ref { expr, mutable })
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
            // Support `T::member` style access where LHS is an explicit type expression
            // (e.g. `dict['k, 'v]::with_capacity`). The member is resolved by name
            // during constraint solving, not during lowering.
            if let Expr::Type(ty) = &scoped_access.lhs.value {
                let member_name = scoped_access
                    .rhs
                    .value
                    .path
                    .name()
                    .unwrap_or_else(|| scoped_access.rhs.value.to_string());

                // Resolve the type via the query system to get fully qualified paths
                // AND map type variables to schema vars. This is needed for impl/trait
                // method lookup during constraint solving.
                let lhs_ty = ty
                    .root_id()
                    .and_then(|id| ctx.env.resolved_expr_ty(id))
                    .unwrap_or_else(|| ty.value().mono().clone());

                // Record the scoped access with the resolved type info. Method resolution
                // happens during constraint solving via ResolveCall constraints.
                ctx.record_expr(
                    node,
                    ExprKind::ScopedAccess {
                        member_name,
                        lhs_ty,
                    },
                )
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
        Expr::Type(ty_scheme) => {
            let ty = ty_scheme
                .root_id()
                .and_then(|id| ctx.env.resolved_expr_ty(id))
                .unwrap_or_else(|| ty_scheme.value().mono().clone());
            ctx.record_expr(node, ExprKind::Type { ty })
        }
        Expr::TypeAnnotated(value, _) => {
            let expr = lower_expr(ctx, value);
            ctx.record_expr(node, ExprKind::Wrapper { expr })
        }
        Expr::UnaryOp(unary) => {
            let expr = lower_expr(ctx, &unary.expr);
            let op_sym = unary.op.to_string();
            if let Some((trait_fqn, method_fqn)) = ctx.env.prefix_op(&op_sym) {
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
        AstPattern::Name(_) => {
            // Get LocalBindingId from resolutions
            let local_id = match ctx.resolutions.get(&pat.id) {
                Some(Resolution::Local(local_id)) => *local_id,
                _ => {
                    log::debug!("Guard pattern {:?} not found in resolutions", pat.id);
                    return Pattern::Wild;
                }
            };
            // Record the pattern so ty_of(node_id) works
            ctx.record_pattern(pat, PatternKind::Binding { binding: local_id });
            Pattern::Binding {
                node_id: pat.id,
                local_id,
            }
        }
        AstPattern::Some(inner) => match &inner.value {
            AstPattern::Name(_) => {
                // Get LocalBindingId from resolutions
                let local_id = match ctx.resolutions.get(&inner.id) {
                    Some(Resolution::Local(local_id)) => *local_id,
                    _ => {
                        log::debug!("Some pattern inner {:?} not found in resolutions", inner.id);
                        return Pattern::Wild;
                    }
                };
                // Record the inner binding pattern
                ctx.record_pattern(inner, PatternKind::Binding { binding: local_id });
                // Record the outer `some(x)` pattern - its type is nilable(inner_ty)
                ctx.record_pattern(pat, PatternKind::Some { binding: local_id });
                Pattern::Some {
                    outer_node_id: pat.id,
                    inner_node_id: inner.id,
                    local_id,
                }
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
    use ray_shared::{
        def::DefId,
        file_id::FileId,
        node_id::{NodeId, NodeIdGuard},
        pathlib::{FilePath, Path as RayPath},
        span::{Source as RaySource, Span},
    };

    use crate::{
        ast::{Block, Decl, Expr, Func, Literal, Node},
        sourcemap::SourceMap,
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
    #[ignore = "uses legacy code"]
    fn lower_simple_bool_function_into_module_input() {
        todo!("FIXME: this uses legacy code that needs to be migrated to the query system");

        // let _guard = test_def_context();
        // // Build a minimal module with a single function:
        // //
        // //   fn f() { true }
        // //
        // // and ensure it lowers into a ModuleInput with:
        // // - one BindingId for `f`
        // // - a root expression of kind LiteralBool(true).

        // // Function path `f`
        // let func_path = Node::new(RayPath::from("f"));
        // let func_body_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        // let func_body_block = Node::new(Expr::Block(Block {
        //     stmts: vec![func_body_expr.clone()],
        // }));
        // let func = Func::new(func_path, vec![], func_body_block);
        // let func_decl = Node::new(Decl::Func(func));

        // let module: Module<(), Decl> = Module {
        //     path: RayPath::from("test"),
        //     stmts: vec![],
        //     decls: vec![func_decl],
        //     imports: vec![],
        //     import_stmts: vec![],
        //     submodules: vec![],
        //     doc_comment: None,
        //     root_filepath: FilePath::from("test.ray"),
        //     filepaths: vec![FilePath::from("test.ray")],
        //     is_lib: false,
        // };

        // let mut srcmap = SourceMap::new();
        // srcmap.set_src(&func_body_expr, make_test_source());

        // let resolutions: HashMap<NodeId, Resolution> = HashMap::new();
        // let typecheck_env = MockTypecheckEnv::new();
        // let def_ids = collect_def_ids(&module);
        // let def_bindings = build_binding_graph(&def_ids, &resolutions);
        // let input = build_typecheck_input(
        //     &module.decls,
        //     &[],
        //     &srcmap,
        //     &typecheck_env,
        //     &resolutions,
        //     def_bindings,
        // );

        // // There should be exactly one def_node entry.
        // assert_eq!(input.def_nodes.len(), 1);
        // let (&def_id, &root_expr) = input.def_nodes.iter().next().unwrap();

        // // The binding graph should know about this binding.
        // assert!(input.bindings.edges.contains_key(&def_id));

        // // The root expression should be a zero-arg function whose body is the bool literal.
        // let kind = input.expr_kind(root_expr).unwrap();
        // match kind {
        //     ExprKind::Function { params, body } => {
        //         assert!(params.is_empty(), "expected zero params");
        //         let body_kind = input.expr_kind(*body).unwrap();
        //         match body_kind {
        //             ExprKind::Sequence { items } => {
        //                 assert_eq!(items.len(), 1, "expected single statement in block");
        //                 let lit_kind = input.expr_kind(items[0]).unwrap();
        //                 match lit_kind {
        //                     ExprKind::LiteralBool(true) => {}
        //                     other => panic!("expected LiteralBool(true), got {:?}", other),
        //                 }
        //             }
        //             other => panic!("expected sequence block, got {:?}", other),
        //         }
        //     }
        //     other => panic!("expected function wrapper, got {:?}", other),
        // }
    }

    #[test]
    #[ignore = "needs migration to query-based typecheck"]
    fn typecheck_simple_bool_function_with_new_typechecker() {
        let _guard = test_def_context();

        let func_path = Node::new(RayPath::from("g"));
        let func_body_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let func_body_block = Node::new(Expr::Block(Block {
            stmts: vec![func_body_expr.clone()],
        }));
        let func = Func::new(func_path, vec![], func_body_block);
        let _func_decl = Node::new(Decl::Func(func));

        let mut srcmap = SourceMap::new();
        srcmap.set_src(&func_body_expr, make_test_source());

        todo!("FIXME: uses legacy code that needs to be replaced")

        // let mut pass_manager = FrontendPassManager::new(&module, &srcmap, &mut tcx, &resolutions);
        // let result = pass_manager.typecheck(&ncx, options).clone();

        // assert!(
        //     result.errors.is_empty(),
        //     "expected no type errors, got {:?}",
        //     result.errors
        // );
    }

    #[test]
    #[ignore = "needs migration to query-based typecheck"]
    fn typecheck_boxed_bool_function_with_new_typechecker() {
        todo!("FIXME: uses legacy code that needs to be replaced")

        // let _guard = test_def_context();
        // // fn b() { box true }
        // //
        // // This exercises lowering of Boxed and the Boxed => *T rule in the
        // // constraint generator.

        // let func_path = Node::new(RayPath::from("b"));

        // let inner_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        // let boxed_expr = Node::new(Expr::Boxed(Boxed {
        //     inner: Box::new(inner_expr.clone()),
        //     box_span: Span::new(),
        // }));

        // let func_body_block = Node::new(Expr::Block(Block {
        //     stmts: vec![boxed_expr.clone()],
        // }));
        // let func = Func::new(func_path, vec![], func_body_block);
        // let func_decl = Node::new(Decl::Func(func));

        // let module: Module<(), Decl> = Module {
        //     path: RayPath::from("test_boxed"),
        //     stmts: vec![],
        //     decls: vec![func_decl],
        //     imports: vec![],
        //     import_stmts: vec![],
        //     submodules: vec![],
        //     doc_comment: None,
        //     root_filepath: FilePath::from("test_boxed.ray"),
        //     filepaths: vec![FilePath::from("test_boxed.ray")],
        //     is_lib: false,
        // };

        // let mut srcmap = SourceMap::new();
        // srcmap.set_src(&boxed_expr, make_test_source());

        // let global_env = GlobalEnv::new();
        // let mut tcx = TyCtx::new(global_env);
        // let ncx = NameContext::new();
        // let options = TypecheckOptions::default();
        // let resolutions: HashMap<NodeId, Resolution> = HashMap::new();

        // let mut pass_manager = FrontendPassManager::new(&module, &srcmap, &mut tcx, &resolutions);
        // let result = pass_manager.typecheck(&ncx, options).clone();

        // assert!(
        //     result.errors.is_empty(),
        //     "expected no type errors for boxed bool, got {:?}",
        //     result.errors
        // );
    }
}

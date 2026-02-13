//! Expected type query for LSP smart completion.
//!
//! The `expected_type_at` query infers what type is expected at a given position
//! based on the surrounding AST context. For example, if the cursor is on a
//! function argument, the expected type is the corresponding parameter type.
//!
//! This is a best-effort query: it returns `None` when no type expectation can
//! be inferred (e.g. no interesting context, type errors, or incomplete code).

use ray_core::{
    ast::{CurlyElement, Decl, Expr, File, Node},
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::{
    file_id::FileId,
    node_id::NodeId,
    resolution::{DefTarget, Resolution},
    span::Pos,
    ty::Ty,
};

use crate::{
    queries::{
        libraries::LoadedLibraries, parse::parse_file, resolve::name_resolutions, typecheck::ty_of,
        types::annotated_scheme,
    },
    query::{Database, Query},
};

/// The context that determines what type is expected at a position.
///
/// Produced by the top-down AST walk, then resolved to an actual `Ty`
/// using `ty_of` lookups.
#[derive(Debug, Clone)]
enum ExpectedTypeContext {
    /// Position is a call argument at the given index.
    CallArg { callee_id: NodeId, arg_index: usize },

    /// Position is the right-hand side of an assignment.
    AssignRhs { lhs_id: NodeId },

    /// Position is inside a return expression.
    ReturnExpr { func_node_id: NodeId },

    /// Position is an element in a list literal.
    ListElement { list_id: NodeId },
}

/// Returns the expected type at a given position in a file.
///
/// Walks the raw parsed AST (`parse_file`) to determine the surrounding context
/// (function argument, assignment RHS, return expression, or list element),
/// then resolves that context to a concrete type using `ty_of`.
///
/// Uses the raw parsed AST because positions correspond to what the user sees
/// in their editor, and synthetic nodes from transformation may not have
/// meaningful source spans.
///
/// Returns `None` when no type expectation can be inferred.
#[query]
pub fn expected_type_at(db: &Database, file_id: FileId, pos: Pos) -> Option<Ty> {
    let parsed = parse_file(db, file_id);
    let context = find_context(&parsed.ast, &parsed.source_map, &pos)?;
    resolve_context(db, &context)
}

/// Resolve an `ExpectedTypeContext` to a concrete `Ty` using type queries.
fn resolve_context(db: &Database, ctx: &ExpectedTypeContext) -> Option<Ty> {
    match ctx {
        ExpectedTypeContext::CallArg {
            callee_id,
            arg_index,
        } => callee_declared_type(db, callee_id)?
            .get_func_param(*arg_index)
            .cloned(),

        ExpectedTypeContext::AssignRhs { lhs_id } => ty_of(db, *lhs_id),

        ExpectedTypeContext::ReturnExpr { func_node_id } => {
            ty_of(db, *func_node_id)?.get_fn_ret_ty().cloned()
        }

        ExpectedTypeContext::ListElement { list_id } => {
            ty_of(db, *list_id)?.type_argument_at(0).cloned()
        }
    }
}

/// Get the declared type of a callee expression.
///
/// Resolves the callee's name to its definition and retrieves the declared
/// function type. This is more reliable than `ty_of` at the call site, which
/// may infer a wrong arity when arguments are missing (the completion case).
///
/// Falls back to `ty_of` for local bindings (closures, function variables)
/// where no declaration is available.
fn callee_declared_type(db: &Database, callee_id: &NodeId) -> Option<Ty> {
    let file_id = callee_id.owner.file;
    let resolutions = name_resolutions(db, file_id);

    match resolutions.get(callee_id) {
        Some(Resolution::Def(DefTarget::Workspace(def_id))) => {
            annotated_scheme(db, *def_id).map(|s| s.ty)
        }
        Some(Resolution::Def(DefTarget::Library(lib_id))) => {
            let libs = db.get_input::<LoadedLibraries>(());
            libs.libraries
                .get(&lib_id.module)
                .and_then(|data| data.schemes.get(lib_id))
                .map(|s| s.ty.clone())
        }
        _ => {
            // Local bindings, primitives, unresolved names — use ty_of as
            // best-effort fallback.
            ty_of(db, *callee_id)
        }
    }
}

/// Walk the AST top-down to find the expected type context at `pos`.
///
/// Tracks the enclosing function's NodeId for resolving return expressions.
/// At each "context-setting" parent (Call, Assign, Return, List), records the
/// context and recurses. The innermost (deepest) context wins.
fn find_context(file: &File, srcmap: &SourceMap, pos: &Pos) -> Option<ExpectedTypeContext> {
    for decl in &file.decls {
        if let Some(ctx) = find_context_in_decl(decl, srcmap, pos, None) {
            return Some(ctx);
        }
    }

    for stmt in &file.stmts {
        if let Some(ctx) = find_context_in_expr(stmt, srcmap, pos, None) {
            return Some(ctx);
        }
    }

    None
}

/// Walk a declaration looking for the expected type context at `pos`.
fn find_context_in_decl(
    decl: &Node<Decl>,
    srcmap: &SourceMap,
    pos: &Pos,
    enclosing_func_id: Option<NodeId>,
) -> Option<ExpectedTypeContext> {
    match &decl.value {
        Decl::Func(func) => {
            let span = srcmap.get_by_id(decl.id).and_then(|s| s.span);
            if !span.map_or(false, |s| s.contains_pos(pos)) {
                return None;
            }

            let func_id = Some(decl.id);
            if let Some(body) = &func.body {
                return find_context_in_expr(body, srcmap, pos, func_id);
            }
            None
        }
        Decl::Impl(im) => {
            if let Some(funcs) = &im.funcs {
                for func_decl in funcs {
                    if let Some(ctx) =
                        find_context_in_decl(func_decl, srcmap, pos, enclosing_func_id)
                    {
                        return Some(ctx);
                    }
                }
            }
            None
        }
        Decl::Trait(tr) => {
            for field in &tr.fields {
                if let Some(ctx) = find_context_in_decl(field, srcmap, pos, enclosing_func_id) {
                    return Some(ctx);
                }
            }
            None
        }
        Decl::FileMain(stmts) => {
            for stmt in stmts {
                if let Some(ctx) = find_context_in_expr(stmt, srcmap, pos, enclosing_func_id) {
                    return Some(ctx);
                }
            }
            None
        }
        Decl::Struct(_)
        | Decl::FnSig(_)
        | Decl::TypeAlias(_, _)
        | Decl::Mutable(_, _)
        | Decl::Name(_, _)
        | Decl::Declare(_) => None,
    }
}

/// Walk an expression looking for the expected type context at `pos`.
///
/// Returns the innermost context: if recursion into a child finds a deeper
/// context, that takes priority over the current level's context.
fn find_context_in_expr(
    expr: &Node<Expr>,
    srcmap: &SourceMap,
    pos: &Pos,
    enclosing_func_id: Option<NodeId>,
) -> Option<ExpectedTypeContext> {
    let span = srcmap.get_by_id(expr.id).and_then(|s| s.span);
    if !span.map_or(false, |s| s.contains_pos(pos)) {
        return None;
    }

    match &expr.value {
        // Context-setting parents: these establish an expected type for their children.
        Expr::Call(call) => {
            // Check if pos is in one of the arguments
            for (i, arg) in call.args.items.iter().enumerate() {
                let arg_span = srcmap.get_by_id(arg.id).and_then(|s| s.span);
                if arg_span.map_or(false, |s| s.contains_pos(pos)) {
                    let this_context = ExpectedTypeContext::CallArg {
                        callee_id: call.callee.id,
                        arg_index: i,
                    };
                    let deeper = find_context_in_expr(arg, srcmap, pos, enclosing_func_id);
                    return deeper.or(Some(this_context));
                }
            }

            // Pos is inside the parens but not on any existing argument —
            // this is the completion case (e.g. `foo(a, |)` where | is cursor).
            // The expected type is for the next argument position.
            if call.paren_span.contains_pos(pos) {
                return Some(ExpectedTypeContext::CallArg {
                    callee_id: call.callee.id,
                    arg_index: call.args.items.len(),
                });
            }

            // Pos might be in the callee expression
            find_context_in_expr(&call.callee, srcmap, pos, enclosing_func_id)
        }

        Expr::Assign(assign) => {
            let rhs_span = srcmap.get_by_id(assign.rhs.id).and_then(|s| s.span);
            if rhs_span.map_or(false, |s| s.contains_pos(pos)) {
                let this_context = ExpectedTypeContext::AssignRhs {
                    lhs_id: assign.lhs.id,
                };
                let deeper = find_context_in_expr(&assign.rhs, srcmap, pos, enclosing_func_id);
                return deeper.or(Some(this_context));
            }
            None
        }

        Expr::Return(Some(inner)) => {
            let inner_span = srcmap.get_by_id(inner.id).and_then(|s| s.span);
            if inner_span.map_or(false, |s| s.contains_pos(pos)) {
                let this_context = enclosing_func_id
                    .map(|fid| ExpectedTypeContext::ReturnExpr { func_node_id: fid });
                let deeper = find_context_in_expr(inner, srcmap, pos, enclosing_func_id);
                return deeper.or(this_context);
            }
            None
        }

        Expr::List(list) => {
            for item in &list.items {
                let item_span = srcmap.get_by_id(item.id).and_then(|s| s.span);
                if item_span.map_or(false, |s| s.contains_pos(pos)) {
                    let this_context = ExpectedTypeContext::ListElement { list_id: expr.id };
                    let deeper = find_context_in_expr(item, srcmap, pos, enclosing_func_id);
                    return deeper.or(Some(this_context));
                }
            }
            None
        }

        // Scope-creating expressions: update enclosing function, recurse into body.
        Expr::Func(func) => {
            let func_id = Some(expr.id);
            if let Some(body) = &func.body {
                return find_context_in_expr(body, srcmap, pos, func_id);
            }
            None
        }

        Expr::Closure(closure) => {
            find_context_in_expr(&closure.body, srcmap, pos, enclosing_func_id)
        }

        // Recursion-only expressions: just recurse into children.
        Expr::Block(block) => {
            for stmt in &block.stmts {
                if let Some(ctx) = find_context_in_expr(stmt, srcmap, pos, enclosing_func_id) {
                    return Some(ctx);
                }
            }
            None
        }

        Expr::If(if_expr) => {
            if let Some(ctx) = find_context_in_expr(&if_expr.cond, srcmap, pos, enclosing_func_id) {
                return Some(ctx);
            }
            if let Some(ctx) = find_context_in_expr(&if_expr.then, srcmap, pos, enclosing_func_id) {
                return Some(ctx);
            }
            if let Some(els) = &if_expr.els {
                if let Some(ctx) = find_context_in_expr(els, srcmap, pos, enclosing_func_id) {
                    return Some(ctx);
                }
            }
            None
        }

        Expr::While(while_expr) => {
            find_context_in_expr(&while_expr.cond, srcmap, pos, enclosing_func_id)
                .or_else(|| find_context_in_expr(&while_expr.body, srcmap, pos, enclosing_func_id))
        }

        Expr::Loop(loop_expr) => {
            find_context_in_expr(&loop_expr.body, srcmap, pos, enclosing_func_id)
        }

        Expr::For(for_expr) => find_context_in_expr(&for_expr.expr, srcmap, pos, enclosing_func_id)
            .or_else(|| find_context_in_expr(&for_expr.body, srcmap, pos, enclosing_func_id)),

        Expr::BinOp(binop) => find_context_in_expr(&binop.lhs, srcmap, pos, enclosing_func_id)
            .or_else(|| find_context_in_expr(&binop.rhs, srcmap, pos, enclosing_func_id)),

        Expr::Paren(inner)
        | Expr::Some(inner)
        | Expr::DefaultValue(inner)
        | Expr::Unsafe(inner) => find_context_in_expr(inner, srcmap, pos, enclosing_func_id),

        Expr::Boxed(boxed) => find_context_in_expr(&boxed.inner, srcmap, pos, enclosing_func_id),

        Expr::Return(None) | Expr::Break(None) => None,

        Expr::Break(Some(inner)) => find_context_in_expr(inner, srcmap, pos, enclosing_func_id),

        Expr::Dot(dot) => find_context_in_expr(&dot.lhs, srcmap, pos, enclosing_func_id),

        Expr::Index(index) => find_context_in_expr(&index.lhs, srcmap, pos, enclosing_func_id)
            .or_else(|| find_context_in_expr(&index.index, srcmap, pos, enclosing_func_id)),

        Expr::TypeAnnotated(inner, _) | Expr::Labeled(_, inner) => {
            find_context_in_expr(inner, srcmap, pos, enclosing_func_id)
        }

        Expr::Cast(cast) => find_context_in_expr(&cast.lhs, srcmap, pos, enclosing_func_id),

        Expr::Deref(deref) => find_context_in_expr(&deref.expr, srcmap, pos, enclosing_func_id),

        Expr::Ref(rf) => find_context_in_expr(&rf.expr, srcmap, pos, enclosing_func_id),

        Expr::UnaryOp(unary) => find_context_in_expr(&unary.expr, srcmap, pos, enclosing_func_id),

        Expr::Range(range) => find_context_in_expr(&range.start, srcmap, pos, enclosing_func_id)
            .or_else(|| find_context_in_expr(&range.end, srcmap, pos, enclosing_func_id)),

        Expr::Tuple(tuple) => {
            for item in &tuple.seq.items {
                if let Some(ctx) = find_context_in_expr(item, srcmap, pos, enclosing_func_id) {
                    return Some(ctx);
                }
            }
            None
        }

        Expr::Sequence(seq) => {
            for item in &seq.items {
                if let Some(ctx) = find_context_in_expr(item, srcmap, pos, enclosing_func_id) {
                    return Some(ctx);
                }
            }
            None
        }

        Expr::ScopedAccess(sa) => find_context_in_expr(&sa.lhs, srcmap, pos, enclosing_func_id),

        Expr::Curly(curly) => {
            for elem in &curly.elements {
                if let CurlyElement::Labeled(_, expr) = &elem.value {
                    if let Some(ctx) = find_context_in_expr(expr, srcmap, pos, enclosing_func_id) {
                        return Some(ctx);
                    }
                }
            }
            None
        }

        Expr::Dict(dict) => {
            for (k, v) in &dict.entries {
                if let Some(ctx) = find_context_in_expr(k, srcmap, pos, enclosing_func_id) {
                    return Some(ctx);
                }
                if let Some(ctx) = find_context_in_expr(v, srcmap, pos, enclosing_func_id) {
                    return Some(ctx);
                }
            }
            None
        }

        Expr::Set(set) => {
            for item in &set.items {
                if let Some(ctx) = find_context_in_expr(item, srcmap, pos, enclosing_func_id) {
                    return Some(ctx);
                }
            }
            None
        }

        Expr::New(new_expr) => {
            if let Some(count) = &new_expr.count {
                return find_context_in_expr(count, srcmap, pos, enclosing_func_id);
            }
            None
        }

        // Leaf expressions — no children to recurse into
        Expr::Name(_)
        | Expr::Literal(_)
        | Expr::Continue
        | Expr::Missing(_)
        | Expr::Path(_)
        | Expr::Pattern(_)
        | Expr::Type(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        file_id::FileId,
        pathlib::{FilePath, ModulePath, Path},
        span::Pos,
        ty::Ty,
    };

    use crate::{
        queries::{
            expected_type::expected_type_at,
            libraries::LoadedLibraries,
            workspace::{CompilerOptions, FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_db(source: &str) -> (Database, FileId) {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: true });
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );
        (db, file_id)
    }

    /// Helper: find the byte offset of a substring in the source.
    fn pos_of(source: &str, needle: &str) -> Pos {
        let offset = source.find(needle).expect("needle not found in source");
        let prefix = &source[..offset];
        let lineno = prefix.matches('\n').count();
        let col = match prefix.rfind('\n') {
            Some(nl) => offset - nl - 1,
            None => offset,
        };
        Pos {
            lineno,
            col,
            offset,
        }
    }

    #[test]
    fn expected_type_at_empty_file() {
        let (db, file_id) = setup_db("");
        let pos = Pos {
            lineno: 0,
            col: 0,
            offset: 0,
        };
        let result = expected_type_at(&db, file_id, pos);
        assert!(result.is_none(), "empty file should have no expected type");
    }

    #[test]
    fn expected_type_at_no_context() {
        // Position on a standalone expression, not inside a call/assign/return/list
        let source = r#"
fn main() {
    42
}
"#;
        let (db, file_id) = setup_db(source);
        let pos = pos_of(source, "42");
        let result = expected_type_at(&db, file_id, pos);
        assert!(
            result.is_none(),
            "standalone expression should have no expected type, got: {:?}",
            result
        );
    }

    #[test]
    fn expected_type_at_call_argument() {
        let source = r#"
fn foo(x: int) {}

fn main() {
    foo(42)
}
"#;
        let (db, file_id) = setup_db(source);
        // Position on the `42` argument
        let pos = pos_of(source, "42)");
        let result = expected_type_at(&db, file_id, pos);
        assert!(
            result.is_some(),
            "call argument should have expected type, got None"
        );
        let ty = result.unwrap();
        assert!(
            matches!(ty, Ty::Const(ref p) if p.to_string().contains("int")),
            "expected int type for call argument, got: {:?}",
            ty
        );
    }

    #[test]
    fn expected_type_at_return_expr() {
        let source = r#"
fn foo() -> int {
    return 42
}
"#;
        let (db, file_id) = setup_db(source);
        // Position on the `42` inside return
        let pos = pos_of(source, "42");
        let result = expected_type_at(&db, file_id, pos);
        assert!(
            result.is_some(),
            "return expression should have expected type, got None"
        );
        let ty = result.unwrap();
        assert!(
            matches!(ty, Ty::Const(ref p) if p.to_string().contains("int")),
            "expected int return type, got: {:?}",
            ty
        );
    }

    #[test]
    fn expected_type_at_nested_call() {
        // In `foo(bar(42))`, the expected type at `42` should be bar's parameter type
        let source = r#"
fn bar(y: int) -> int {
    y
}

fn foo(x: int) {}

fn main() {
    foo(bar(42))
}
"#;
        let (db, file_id) = setup_db(source);
        let pos = pos_of(source, "42");
        let result = expected_type_at(&db, file_id, pos);
        assert!(
            result.is_some(),
            "nested call argument should have expected type, got None"
        );
        let ty = result.unwrap();
        assert!(
            matches!(ty, Ty::Const(ref p) if p.to_string().contains("int")),
            "expected int type for bar's parameter, got: {:?}",
            ty
        );
    }

    #[test]
    fn expected_type_at_handles_parse_errors() {
        let source = r#"
fn foo() {}
fn bar( {
"#;
        let (db, file_id) = setup_db(source);
        let pos = pos_of(source, "bar");
        // Should not panic
        let result = expected_type_at(&db, file_id, pos);
        // With broken code, we likely get None
        assert!(
            result.is_none(),
            "broken code should return None, got: {:?}",
            result
        );
    }

    #[test]
    fn expected_type_at_empty_call_argument() {
        // The real completion use case: user types `foo(a, ` and wants to know
        // what type is expected at the empty second argument position.
        let source = r#"
fn foo(x: u32, y: u16) {}

fn main() {
    a: u32 = 21
    foo(a, )
}
"#;
        let (db, file_id) = setup_db(source);
        // Position on the space before `)`, inside the parens but no arg there
        let pos = pos_of(source, " )");
        let result = expected_type_at(&db, file_id, pos);
        assert!(
            result.is_some(),
            "empty argument position should have expected type, got None"
        );
        let ty = result.unwrap();
        assert!(
            matches!(ty, Ty::Const(ref p) if p.to_string().contains("u16")),
            "expected u16 type for empty second argument, got: {:?}",
            ty
        );
    }
}

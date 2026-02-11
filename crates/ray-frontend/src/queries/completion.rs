//! Completion context query for LSP completion.
//!
//! The `completion_context` query analyzes a cursor position to determine what
//! kind of completion is appropriate. It combines scope, expected type, and AST
//! context to produce a `CompletionContext` that the LSP handler can use to
//! generate completion items.
//!
//! Returns `None` when the position doesn't support completion (e.g., inside a
//! string literal or comment).

use std::{collections::HashMap, sync::Arc};

use ray_core::{
    ast::{CurlyElement, Decl, Expr, File, Literal, Node},
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::{
    file_id::FileId,
    node_id::NodeId,
    pathlib::ModulePath,
    resolution::{DefTarget, Resolution},
    scope::ScopeEntry,
    span::Pos,
    ty::Ty,
};

use crate::{
    queries::{
        expected_type::expected_type_at, parse::parse_file, resolve::name_resolutions,
        scope::scope_at, typecheck::ty_of,
    },
    query::{Database, Query},
};

/// What kind of completion is appropriate at the cursor position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompletionKind {
    /// After `.` — complete methods/fields on receiver.
    Member,
    /// Bare identifier — complete from scope.
    Scope,
    /// After `module::` — complete module exports.
    ModuleMember(ModulePath),
    /// After `Type::` — complete associated items.
    TypeMember(DefTarget),
}

/// The full completion context at a cursor position.
///
/// Produced by the `completion_context` query and consumed by the LSP
/// completion handler.
#[derive(Clone, Debug)]
pub struct CompletionContext {
    pub kind: CompletionKind,
    pub scope: Vec<(String, ScopeEntry)>,
    pub receiver_type: Option<Ty>,
    pub expected_type: Option<Ty>,
}

/// Returns the completion context at a given position in a file.
///
/// Combines several sub-queries:
/// - `scope_at` for names visible at the position
/// - `expected_type_at` for the expected type from surrounding context
/// - AST walk + `ty_of` / `name_resolutions` for determining the completion kind
///
/// Returns `None` if the position doesn't support completion (e.g., inside a
/// string literal).
#[query]
pub fn completion_context(db: &Database, file_id: FileId, pos: Pos) -> Option<CompletionContext> {
    let scope = scope_at(db, file_id, pos);
    let expected_type = expected_type_at(db, file_id, pos);

    let parsed = parse_file(db, file_id);
    let resolutions = name_resolutions(db, file_id);

    let position_ctx = find_position_context(&parsed.ast, &parsed.source_map, &pos);

    match position_ctx {
        Some(PositionContext::StringLiteral) => None,

        Some(PositionContext::DotAccess { receiver_id }) => {
            let receiver_type = ty_of(db, receiver_id);
            Some(CompletionContext {
                kind: CompletionKind::Member,
                scope: (*scope).clone(),
                receiver_type,
                expected_type,
            })
        }

        Some(PositionContext::ScopedAccess { lhs_id }) => {
            let kind = resolve_scoped_access_kind(lhs_id, &resolutions, &scope);
            Some(CompletionContext {
                kind,
                scope: (*scope).clone(),
                receiver_type: None,
                expected_type,
            })
        }

        Some(PositionContext::PathAccess { first_segment }) => {
            let kind = resolve_path_access_kind(&first_segment, &scope);
            Some(CompletionContext {
                kind,
                scope: (*scope).clone(),
                receiver_type: None,
                expected_type,
            })
        }

        Some(PositionContext::General) | None => Some(CompletionContext {
            kind: CompletionKind::Scope,
            scope: (*scope).clone(),
            receiver_type: None,
            expected_type,
        }),
    }
}

/// Determine the `CompletionKind` for a `ScopedAccess` by resolving the LHS.
///
/// Checks name resolution first (for type definitions), then falls back to
/// checking the scope for module entries.
fn resolve_scoped_access_kind(
    lhs_id: NodeId,
    resolutions: &HashMap<NodeId, Resolution>,
    scope: &Arc<Vec<(String, ScopeEntry)>>,
) -> CompletionKind {
    // Check name resolution: if the LHS resolves to a definition, it's a type.
    if let Some(Resolution::Def(def_target)) = resolutions.get(&lhs_id) {
        return CompletionKind::TypeMember(def_target.clone());
    }

    // Check scope for module entries. Extract the name from the resolution
    // error (which contains the name string) or fall back to Scope.
    if let Some(Resolution::Error { name, .. }) = resolutions.get(&lhs_id) {
        for (scope_name, entry) in scope.iter() {
            if scope_name == name {
                if let ScopeEntry::Module(module_path) = entry {
                    return CompletionKind::ModuleMember(module_path.clone());
                }
            }
        }
    }

    // Fallback: treat as scope completion.
    CompletionKind::Scope
}

/// Determine the `CompletionKind` for a `Path` expression by looking up the
/// first segment in scope.
///
/// The parser produces `Expr::Path(["Point", "new"])` for `Point::new` syntax.
/// We look up the first segment ("Point") in scope to determine if it's a
/// module or type definition.
fn resolve_path_access_kind(
    first_segment: &str,
    scope: &Arc<Vec<(String, ScopeEntry)>>,
) -> CompletionKind {
    for (name, entry) in scope.iter() {
        if name == first_segment {
            return match entry {
                ScopeEntry::Module(module_path) => {
                    CompletionKind::ModuleMember(module_path.clone())
                }
                ScopeEntry::Def(def_target) => CompletionKind::TypeMember(def_target.clone()),
                _ => CompletionKind::Scope,
            };
        }
    }
    CompletionKind::Scope
}

/// Internal result of the AST walk: what kind of position the cursor is at.
enum PositionContext {
    /// After `.` — cursor is on the RHS of a member access.
    DotAccess { receiver_id: NodeId },
    /// After `::` — cursor is on the RHS of a scoped access (postfix form).
    ScopedAccess { lhs_id: NodeId },
    /// Inside a qualified path like `Point::new` or `utils::helper`.
    /// The parser produces `Expr::Path` for `Name::Name` syntax.
    /// `first_segment` is the name of the first path segment (e.g., "Point").
    PathAccess { first_segment: String },
    /// Inside a string literal — no completion.
    StringLiteral,
    /// Any other position — bare identifier or general expression.
    General,
}

/// Walk the AST to determine what kind of position the cursor is at.
fn find_position_context(file: &File, srcmap: &SourceMap, pos: &Pos) -> Option<PositionContext> {
    for decl in &file.decls {
        if let Some(ctx) = find_ctx_in_decl(decl, srcmap, pos) {
            return Some(ctx);
        }
    }

    for stmt in &file.stmts {
        if let Some(ctx) = find_ctx_in_expr(stmt, srcmap, pos) {
            return Some(ctx);
        }
    }

    None
}

/// Walk a declaration looking for the position context.
fn find_ctx_in_decl(decl: &Node<Decl>, srcmap: &SourceMap, pos: &Pos) -> Option<PositionContext> {
    match &decl.value {
        Decl::Func(func) => {
            let span = srcmap.get_by_id(decl.id).and_then(|s| s.span);
            if !span.map_or(false, |s| s.contains_pos(pos)) {
                return None;
            }
            if let Some(body) = &func.body {
                return find_ctx_in_expr(body, srcmap, pos);
            }
            None
        }
        Decl::Impl(im) => {
            if let Some(funcs) = &im.funcs {
                for func_decl in funcs {
                    if let Some(ctx) = find_ctx_in_decl(func_decl, srcmap, pos) {
                        return Some(ctx);
                    }
                }
            }
            None
        }
        Decl::Trait(tr) => {
            for field in &tr.fields {
                if let Some(ctx) = find_ctx_in_decl(field, srcmap, pos) {
                    return Some(ctx);
                }
            }
            None
        }
        Decl::FileMain(stmts) => {
            for stmt in stmts {
                if let Some(ctx) = find_ctx_in_expr(stmt, srcmap, pos) {
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

/// Walk an expression to determine the position context.
///
/// At each level, checks if the cursor is at a "special" position (dot access,
/// scoped access, string literal). Returns the innermost match.
fn find_ctx_in_expr(expr: &Node<Expr>, srcmap: &SourceMap, pos: &Pos) -> Option<PositionContext> {
    let span = srcmap.get_by_id(expr.id).and_then(|s| s.span);
    if !span.map_or(false, |s| s.contains_pos(pos)) {
        return None;
    }

    match &expr.value {
        Expr::Dot(dot) => {
            // Check if pos is after the dot token — that's member completion.
            if pos.offset >= dot.dot.span.end.offset {
                return Some(PositionContext::DotAccess {
                    receiver_id: dot.lhs.id,
                });
            }

            // Pos is on the LHS side of the dot — recurse into LHS.
            find_ctx_in_expr(&dot.lhs, srcmap, pos)
        }

        Expr::ScopedAccess(sa) => {
            // Check if pos is after the `::` separator — that's scoped access completion.
            if pos.offset >= sa.sep.span.end.offset {
                return Some(PositionContext::ScopedAccess { lhs_id: sa.lhs.id });
            }

            // Pos is on the LHS side — recurse.
            find_ctx_in_expr(&sa.lhs, srcmap, pos)
        }

        Expr::Literal(lit) => {
            if matches!(lit, Literal::String(_) | Literal::ByteString(_)) {
                return Some(PositionContext::StringLiteral);
            }
            Some(PositionContext::General)
        }

        // Recurse into children for compound expressions.
        Expr::Call(call) => {
            for arg in &call.args.items {
                if let Some(ctx) = find_ctx_in_expr(arg, srcmap, pos) {
                    return Some(ctx);
                }
            }
            find_ctx_in_expr(&call.callee, srcmap, pos)
        }

        Expr::Assign(assign) => find_ctx_in_expr(&assign.rhs, srcmap, pos),

        Expr::Block(block) => {
            for stmt in &block.stmts {
                if let Some(ctx) = find_ctx_in_expr(stmt, srcmap, pos) {
                    return Some(ctx);
                }
            }
            None
        }

        Expr::If(if_expr) => find_ctx_in_expr(&if_expr.cond, srcmap, pos)
            .or_else(|| find_ctx_in_expr(&if_expr.then, srcmap, pos))
            .or_else(|| {
                if_expr
                    .els
                    .as_ref()
                    .and_then(|els| find_ctx_in_expr(els, srcmap, pos))
            }),

        Expr::While(while_expr) => find_ctx_in_expr(&while_expr.cond, srcmap, pos)
            .or_else(|| find_ctx_in_expr(&while_expr.body, srcmap, pos)),

        Expr::Loop(loop_expr) => find_ctx_in_expr(&loop_expr.body, srcmap, pos),

        Expr::For(for_expr) => find_ctx_in_expr(&for_expr.expr, srcmap, pos)
            .or_else(|| find_ctx_in_expr(&for_expr.body, srcmap, pos)),

        Expr::Func(func) => func
            .body
            .as_ref()
            .and_then(|body| find_ctx_in_expr(body, srcmap, pos)),

        Expr::Closure(closure) => find_ctx_in_expr(&closure.body, srcmap, pos),

        Expr::BinOp(binop) => find_ctx_in_expr(&binop.lhs, srcmap, pos)
            .or_else(|| find_ctx_in_expr(&binop.rhs, srcmap, pos)),

        Expr::Paren(inner)
        | Expr::Some(inner)
        | Expr::DefaultValue(inner)
        | Expr::Unsafe(inner) => find_ctx_in_expr(inner, srcmap, pos),

        Expr::Boxed(boxed) => find_ctx_in_expr(&boxed.inner, srcmap, pos),

        Expr::Return(val) | Expr::Break(val) => val
            .as_ref()
            .and_then(|inner| find_ctx_in_expr(inner, srcmap, pos)),

        Expr::Index(index) => find_ctx_in_expr(&index.lhs, srcmap, pos)
            .or_else(|| find_ctx_in_expr(&index.index, srcmap, pos)),

        Expr::TypeAnnotated(inner, _) | Expr::Labeled(_, inner) => {
            find_ctx_in_expr(inner, srcmap, pos)
        }

        Expr::Cast(cast) => find_ctx_in_expr(&cast.lhs, srcmap, pos),

        Expr::Deref(deref) => find_ctx_in_expr(&deref.expr, srcmap, pos),

        Expr::Ref(rf) => find_ctx_in_expr(&rf.expr, srcmap, pos),

        Expr::UnaryOp(unary) => find_ctx_in_expr(&unary.expr, srcmap, pos),

        Expr::Range(range) => find_ctx_in_expr(&range.start, srcmap, pos)
            .or_else(|| find_ctx_in_expr(&range.end, srcmap, pos)),

        Expr::Tuple(tuple) => {
            for item in &tuple.seq.items {
                if let Some(ctx) = find_ctx_in_expr(item, srcmap, pos) {
                    return Some(ctx);
                }
            }
            None
        }

        Expr::List(list) => {
            for item in &list.items {
                if let Some(ctx) = find_ctx_in_expr(item, srcmap, pos) {
                    return Some(ctx);
                }
            }
            None
        }

        Expr::Sequence(seq) => {
            for item in &seq.items {
                if let Some(ctx) = find_ctx_in_expr(item, srcmap, pos) {
                    return Some(ctx);
                }
            }
            None
        }

        Expr::Curly(curly) => {
            for elem in &curly.elements {
                if let CurlyElement::Labeled(_, expr) = &elem.value {
                    if let Some(ctx) = find_ctx_in_expr(expr, srcmap, pos) {
                        return Some(ctx);
                    }
                }
            }
            None
        }

        Expr::Dict(dict) => {
            for (k, v) in &dict.entries {
                if let Some(ctx) = find_ctx_in_expr(k, srcmap, pos) {
                    return Some(ctx);
                }
                if let Some(ctx) = find_ctx_in_expr(v, srcmap, pos) {
                    return Some(ctx);
                }
            }
            None
        }

        Expr::Set(set) => {
            for item in &set.items {
                if let Some(ctx) = find_ctx_in_expr(item, srcmap, pos) {
                    return Some(ctx);
                }
            }
            None
        }

        Expr::New(new_expr) => new_expr
            .count
            .as_ref()
            .and_then(|count| find_ctx_in_expr(count, srcmap, pos)),

        // Multi-segment path like `Point::new` or `utils::helper`.
        // If the cursor is on a non-first segment, it's a path access.
        Expr::Path(segments) if segments.len() >= 2 => {
            // Check if cursor is on a segment after the first one.
            for seg in segments.iter().skip(1) {
                let seg_span = srcmap.get_by_id(seg.id).and_then(|s| s.span);
                if seg_span.map_or(false, |s| s.contains_pos(pos)) {
                    return Some(PositionContext::PathAccess {
                        first_segment: segments[0].value.clone(),
                    });
                }
            }
            Some(PositionContext::General)
        }

        // Leaf expressions
        Expr::Name(_) | Expr::Path(_) | Expr::Pattern(_) | Expr::Type(_) => {
            Some(PositionContext::General)
        }

        Expr::Continue | Expr::Missing(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        file_id::FileId,
        pathlib::{FilePath, Path},
        scope::ScopeEntry,
        span::Pos,
        ty::Ty,
    };

    use crate::{
        queries::{
            completion::{CompletionKind, completion_context},
            libraries::LoadedLibraries,
            workspace::{CompilerOptions, FileSource, WorkspaceSnapshot},
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
        (db, file_id)
    }

    /// Helper: find the byte offset of the start of a substring.
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

    /// Helper: find the byte offset right AFTER a substring ends.
    /// This represents where the cursor would be after typing the needle.
    fn pos_after(source: &str, needle: &str) -> Pos {
        let start = source.find(needle).expect("needle not found in source");
        let offset = start + needle.len();
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

    // ---------------------------------------------------------------
    // Real-world LSP scenarios: incomplete code (the primary use case)
    // ---------------------------------------------------------------

    #[test]
    fn incomplete_dot_access() {
        // User types `x.` and triggers completion — nothing after the dot.
        // This is THE most common completion scenario.
        let source = r#"
struct Foo {}

fn bar(x: Foo) {
    x.
}
"#;
        let (db, file_id) = setup_db(source);
        let pos = pos_after(source, "x.");
        let ctx =
            completion_context(&db, file_id, pos).expect("should return completion after dot");
        assert_eq!(ctx.kind, CompletionKind::Member);
        assert!(
            ctx.receiver_type.is_some(),
            "dot completion should have receiver type"
        );
    }

    #[test]
    fn incomplete_scoped_access_on_type() {
        // User types `Point::` and triggers completion — nothing after `::`.
        let source = r#"
struct Point { x: int, y: int }

fn main() {
    Point::
}
"#;
        let (db, file_id) = setup_db(source);
        let pos = pos_after(source, "Point::");
        let ctx = completion_context(&db, file_id, pos).expect("should return completion after ::");
        assert!(
            matches!(ctx.kind, CompletionKind::TypeMember(_)),
            "Point:: should be TypeMember, got: {:?}",
            ctx.kind
        );
    }

    #[test]
    fn incomplete_module_access() {
        // User types `utils::` and triggers completion — nothing after `::`.
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let file_main = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        let file_utils = workspace.add_file(FilePath::from("utils.ray"), Path::from("utils"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: true });

        let source_main = "import utils\nfn main() {\n    utils::\n}";
        let source_utils = "fn helper() {}";
        FileSource::new(&db, file_main, source_main.to_string());
        FileSource::new(&db, file_utils, source_utils.to_string());

        let pos = pos_after(source_main, "utils::");
        let ctx = completion_context(&db, file_main, pos)
            .expect("should return completion after module::");
        assert!(
            matches!(ctx.kind, CompletionKind::ModuleMember(_)),
            "utils:: should be ModuleMember, got: {:?}",
            ctx.kind
        );
    }

    #[test]
    fn chained_dot_incomplete() {
        // User types `x.y.` — incomplete chain, cursor after second dot.
        let source = r#"
struct Foo {}

fn bar(x: Foo) {
    x.y.
}
"#;
        let (db, file_id) = setup_db(source);
        let pos = pos_after(source, "x.y.");
        let ctx = completion_context(&db, file_id, pos)
            .expect("should return completion for chained dot");
        assert_eq!(ctx.kind, CompletionKind::Member);
    }

    #[test]
    fn dot_after_unclosed_call() {
        // User is editing, previous line has unclosed paren, then types `p.`
        let source = r#"
struct Point { x: int, y: int }

fn main() {
    p = Point::create(10, 20
    p.
}
"#;
        let (db, file_id) = setup_db(source);
        let pos = pos_after(source, "p.");
        let ctx = completion_context(&db, file_id, pos)
            .expect("should return completion even after broken previous line");
        assert_eq!(
            ctx.kind,
            CompletionKind::Member,
            "p. after broken line should still be Member"
        );
    }

    // ---------------------------------------------------------------
    // Partial identifier scenarios (user is mid-typing)
    // ---------------------------------------------------------------

    #[test]
    fn partial_dot_access_has_receiver_type() {
        // User types `x.to` — partial member name after dot.
        // Receiver type should be resolved from the struct.
        let source = r#"
struct Foo {}

fn bar(x: Foo) {
    x.to
}
"#;
        let (db, file_id) = setup_db(source);
        let pos = pos_after(source, "x.to");
        let ctx = completion_context(&db, file_id, pos)
            .expect("should return completion for partial member");
        assert_eq!(ctx.kind, CompletionKind::Member);
        let receiver = ctx
            .receiver_type
            .expect("dot completion should have receiver type");
        assert!(
            matches!(&receiver, Ty::Const(p) if p.to_string().contains("Foo")),
            "receiver should be Foo, got: {:?}",
            receiver
        );
    }

    #[test]
    fn partial_scoped_access_on_type() {
        // User types `Point::cr` — partial associated item name.
        let source = r#"
struct Point { x: int, y: int }

fn main() {
    Point::cr
}
"#;
        let (db, file_id) = setup_db(source);
        let pos = pos_after(source, "Point::cr");
        let ctx = completion_context(&db, file_id, pos)
            .expect("should return completion for partial scoped access");
        assert!(
            matches!(ctx.kind, CompletionKind::TypeMember(_)),
            "Point::cr should be TypeMember, got: {:?}",
            ctx.kind
        );
    }

    #[test]
    fn partial_module_access() {
        // User types `utils::hel` — partial module member name.
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let file_main = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        let file_utils = workspace.add_file(FilePath::from("utils.ray"), Path::from("utils"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: true });

        let source_main = "import utils\nfn main() { utils::hel }";
        let source_utils = "fn helper() {}";
        FileSource::new(&db, file_main, source_main.to_string());
        FileSource::new(&db, file_utils, source_utils.to_string());

        let pos = pos_after(source_main, "utils::hel");
        let ctx = completion_context(&db, file_main, pos)
            .expect("should return completion for partial module access");
        assert!(
            matches!(ctx.kind, CompletionKind::ModuleMember(_)),
            "utils::hel should be ModuleMember, got: {:?}",
            ctx.kind
        );
    }

    // ---------------------------------------------------------------
    // Scope completion scenarios
    // ---------------------------------------------------------------

    #[test]
    fn bare_identifier_in_function_body() {
        // User starts typing a new name — scope should include visible functions.
        let source = r#"
fn foo() {}
fn bar() {}

fn main() {
    f
}
"#;
        let (db, file_id) = setup_db(source);
        let pos = pos_of(source, "f\n}");
        let ctx = completion_context(&db, file_id, pos).expect("should return Scope completion");
        assert_eq!(ctx.kind, CompletionKind::Scope);
        let names: Vec<&str> = ctx.scope.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            names.contains(&"foo"),
            "foo should be in scope, got: {:?}",
            names
        );
        assert!(
            names.contains(&"bar"),
            "bar should be in scope, got: {:?}",
            names
        );
    }

    #[test]
    fn scope_includes_locals_before_cursor() {
        // Local bindings defined before cursor should be in scope.
        let source = r#"
fn main() {
    a = 1
    b = 2
    c
}
"#;
        let (db, file_id) = setup_db(source);
        let pos = pos_of(source, "c\n}");
        let ctx = completion_context(&db, file_id, pos).expect("should return Scope completion");
        let local_names: Vec<&str> = ctx
            .scope
            .iter()
            .filter(|(_, e)| matches!(e, ScopeEntry::Local(_)))
            .map(|(n, _)| n.as_str())
            .collect();
        assert!(
            local_names.contains(&"a"),
            "a should be in scope, got: {:?}",
            local_names
        );
        assert!(
            local_names.contains(&"b"),
            "b should be in scope, got: {:?}",
            local_names
        );
    }

    // ---------------------------------------------------------------
    // Suppression / edge cases
    // ---------------------------------------------------------------

    #[test]
    fn no_completion_inside_string() {
        // String literals should suppress completion entirely.
        let source = r#"
fn main() {
    x = "hello world"
}
"#;
        let (db, file_id) = setup_db(source);
        let pos = pos_of(source, "hello");
        let ctx = completion_context(&db, file_id, pos);
        assert!(
            ctx.is_none(),
            "should not complete inside string literal, got: {:?}",
            ctx.as_ref().map(|c| &c.kind)
        );
    }

    #[test]
    fn no_panic_on_broken_code() {
        // Various broken inputs should never panic.
        let sources = ["fn foo() {}\nfn bar( {", "struct {", "fn main() { if }", ""];
        for source in &sources {
            let (db, file_id) = setup_db(source);
            let pos = Pos {
                lineno: 0,
                col: 0,
                offset: 0,
            };
            // Must not panic — result can be Some or None.
            let _ = completion_context(&db, file_id, pos);
        }
    }
}

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

use serde::{Deserialize, Serialize};

use ray_core::{
    ast::{
        CurlyElement, Decl, Export, ExportKind, Expr, FStringPart, File, Import, ImportKind,
        Literal, Node,
    },
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
        expected_type::expected_type_at,
        imports::resolve_module_path,
        libraries::LoadedLibraries,
        parse::parse_file,
        resolve::name_resolutions,
        scope::scope_at,
        typecheck::ty_of,
        workspace::{FileSource, WorkspaceSnapshot},
    },
    query::{Database, Query},
};

/// What kind of completion is appropriate at the cursor position.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompletionKind {
    /// After `.` — complete methods/fields on receiver.
    Member,
    /// Bare identifier — complete from scope.
    Scope,
    /// After `module::` — complete module exports.
    ModuleMember(ModulePath),
    /// After `Type::` — complete associated items.
    TypeMember(DefTarget),
    /// After `import`/`export` keyword — complete available modules.
    ImportModule,
    /// After `import path::` — complete submodules of resolved prefix.
    ImportModulePath { resolved_prefix: ModulePath },
    /// After `with` or `,` — complete exported names from the resolved module.
    ImportName {
        module_path: ModulePath,
        already_imported: Vec<String>,
    },
}

/// The full completion context at a cursor position.
///
/// Produced by the `completion_context` query and consumed by the LSP
/// completion handler.
#[derive(Clone, Debug, Serialize, Deserialize)]
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
    let source = db.get_input::<FileSource>(file_id);

    // Check import/export context first — these use parser-recovered AST nodes
    if let Some(import_kind) =
        detect_import_completion(&parsed.ast, source.as_str(), &pos, db, file_id)
    {
        return Some(CompletionContext {
            kind: import_kind,
            scope: (*scope).clone(),
            receiver_type: None,
            expected_type: None,
        });
    }

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

// ---------------------------------------------------------------------------
// Import/export completion detection
// ---------------------------------------------------------------------------

/// Check if the cursor is within an import or export statement and determine
/// the appropriate completion kind.
///
/// Uses parser-recovered AST nodes: `ImportKind::Incomplete` for bare `import `,
/// `ImportKind::Names(path, [])` for `import x with `, etc.
fn detect_import_completion(
    file: &File,
    source: &str,
    pos: &Pos,
    db: &Database,
    file_id: FileId,
) -> Option<CompletionKind> {
    // Check imports
    for import in &file.imports {
        if let Some(kind) = import_completion_kind(import, source, pos, db, file_id) {
            return Some(kind);
        }
    }

    // Check exports (same logic, different AST type)
    for export in &file.exports {
        if let Some(kind) = export_completion_kind(export, source, pos, db, file_id) {
            return Some(kind);
        }
    }

    None
}

/// Check if cursor is on the same line as the statement and after its start.
fn is_on_statement_line(span: &ray_shared::span::Span, pos: &Pos) -> bool {
    pos.lineno >= span.start.lineno
        && pos.lineno <= span.end.lineno.max(span.start.lineno)
        && pos.offset >= span.start.offset
}

/// Determine completion kind for an import statement at the given cursor position.
fn import_completion_kind(
    import: &Import,
    source: &str,
    pos: &Pos,
    db: &Database,
    file_id: FileId,
) -> Option<CompletionKind> {
    if !is_on_statement_line(&import.span, pos) {
        return None;
    }

    match &import.kind {
        ImportKind::Incomplete => {
            // `import ` with nothing after keyword, or `import ops::` with partial path.
            // Look at source text to distinguish the two cases.
            incomplete_import_kind(source, &import.span, pos, db, file_id)
        }
        ImportKind::Path(path_node) => {
            // Complete import like `import ops`. If cursor is on the path,
            // the user may be editing the module name.
            let path = &path_node.value;
            if pos.offset <= import.span.end.offset {
                // Cursor is on/within the path — suggest modules
                Some(CompletionKind::ImportModule)
            } else {
                // Cursor is past the import — not in import context
                // (But the user might be typing ` with ` which hasn't been parsed yet.
                // For `import ops with `, `with` would be consumed and we'd get Names.)
                let _ = path;
                None
            }
        }
        ImportKind::Names(path_node, names) => {
            // `import ops with ...` — cursor is in the names area
            let path = &path_node.value;
            let module_path = ModulePath::from(path);
            let resolved = resolve_import_module(db, file_id, &module_path);
            let already_imported: Vec<String> =
                names.iter().map(|n| n.value.to_short_name()).collect();
            Some(CompletionKind::ImportName {
                module_path: resolved,
                already_imported,
            })
        }
        ImportKind::Glob(_) | ImportKind::CImport(_, _) => None,
    }
}

/// Determine completion kind for an export statement at the given cursor position.
fn export_completion_kind(
    export: &Export,
    source: &str,
    pos: &Pos,
    db: &Database,
    file_id: FileId,
) -> Option<CompletionKind> {
    if !is_on_statement_line(&export.span, pos) {
        return None;
    }

    match &export.kind {
        ExportKind::Incomplete => incomplete_export_kind(source, &export.span, pos, db, file_id),
        ExportKind::Path(path_node) => {
            let path = &path_node.value;
            if pos.offset <= export.span.end.offset {
                Some(CompletionKind::ImportModule)
            } else {
                let _ = path;
                None
            }
        }
        ExportKind::Names(path_node, names) => {
            let path = &path_node.value;
            let module_path = ModulePath::from(path);
            let resolved = resolve_import_module(db, file_id, &module_path);
            let already_imported: Vec<String> =
                names.iter().map(|n| n.value.to_short_name()).collect();
            Some(CompletionKind::ImportName {
                module_path: resolved,
                already_imported,
            })
        }
        ExportKind::Glob(_) => None,
    }
}

/// For `ImportKind::Incomplete`, extract the partial path from source text
/// to determine if this is a module or submodule completion.
fn incomplete_import_kind(
    source: &str,
    span: &ray_shared::span::Span,
    pos: &Pos,
    db: &Database,
    file_id: FileId,
) -> Option<CompletionKind> {
    // Extract text from after the keyword to the cursor position
    // The span starts at `import` keyword. Skip "import " (7 chars).
    let keyword_end = span.start.offset + 7; // "import " = 7 bytes
    let text_after_keyword = if pos.offset > keyword_end && pos.offset <= source.len() {
        source[keyword_end..pos.offset].trim()
    } else {
        ""
    };

    parse_partial_path_completion(text_after_keyword, db, file_id)
}

/// For `ExportKind::Incomplete`, extract the partial path from source text.
fn incomplete_export_kind(
    source: &str,
    span: &ray_shared::span::Span,
    pos: &Pos,
    db: &Database,
    file_id: FileId,
) -> Option<CompletionKind> {
    // Skip "export " (7 chars)
    let keyword_end = span.start.offset + 7;
    let text_after_keyword = if pos.offset > keyword_end && pos.offset <= source.len() {
        source[keyword_end..pos.offset].trim()
    } else {
        ""
    };

    parse_partial_path_completion(text_after_keyword, db, file_id)
}

/// Given partial text after import/export keyword, determine completion kind.
///
/// Examples:
/// - `""` → ImportModule (just typed the keyword)
/// - `"co"` → ImportModule (partial module name, client does fuzzy matching)
/// - `"core::"` → ImportModulePath with resolved prefix `core`
/// - `"core::i"` → ImportModulePath with resolved prefix `core`
fn parse_partial_path_completion(
    text: &str,
    db: &Database,
    file_id: FileId,
) -> Option<CompletionKind> {
    if text.contains("::") {
        // Has path separator — this is a submodule completion
        let segments: Vec<&str> = text.split("::").collect();
        // Take all complete segments (exclude the last one which may be partial)
        let prefix_segments: Vec<String> = segments
            .iter()
            .take(segments.len().saturating_sub(1))
            .filter(|s| !s.is_empty())
            .map(|s| s.to_string())
            .collect();

        if prefix_segments.is_empty() {
            return Some(CompletionKind::ImportModule);
        }

        let partial = ModulePath::new(prefix_segments);
        let resolved = resolve_import_module(db, file_id, &partial);
        Some(CompletionKind::ImportModulePath {
            resolved_prefix: resolved,
        })
    } else {
        // No path separator — module name completion
        Some(CompletionKind::ImportModule)
    }
}

/// Resolve a module path for import completion, using the standard resolution order.
fn resolve_import_module(db: &Database, file_id: FileId, module_path: &ModulePath) -> ModulePath {
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let libraries = db.get_input::<LoadedLibraries>(());
    let current_module = workspace
        .file_info(file_id)
        .map(|info| info.module_path.clone());

    resolve_module_path(module_path, &workspace, &libraries, current_module.as_ref())
        .unwrap_or_else(|_| module_path.clone())
}

/// Collect all module names available for import from the current file's perspective.
///
/// Returns `(short_name, full_module_path)` pairs. The short name is what the user
/// types in the import statement.
pub fn available_import_modules(db: &Database, file_id: FileId) -> Vec<(String, ModulePath)> {
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let libraries = db.get_input::<LoadedLibraries>(());
    let current_module = workspace
        .file_info(file_id)
        .map(|info| info.module_path.clone());

    let mut results: Vec<(String, ModulePath)> = Vec::new();
    let mut seen = std::collections::HashSet::new();

    // Helper: add a module if its short name hasn't been seen
    let mut add_module = |mp: &ModulePath| {
        if let Some(name) = mp.segments().last() {
            let name = name.clone();
            if seen.insert(name.clone()) {
                results.push((name, mp.clone()));
            }
        }
    };

    // Child modules (if current module is `core`, suggest `core::io`, etc.)
    if let Some(current) = &current_module {
        for mp in workspace.all_module_paths() {
            if mp.segments().len() == current.segments().len() + 1
                && mp.segments().starts_with(current.segments())
            {
                add_module(mp);
            }
        }
        for mp in libraries.all_module_paths() {
            if mp.segments().len() == current.segments().len() + 1
                && mp.segments().starts_with(current.segments())
            {
                add_module(mp);
            }
        }

        // Sibling modules
        if current.segments().len() > 1 {
            let parent = &current.segments()[..current.segments().len() - 1];
            for mp in workspace.all_module_paths() {
                if mp.segments().len() == parent.len() + 1
                    && mp.segments().starts_with(parent)
                    && mp != current
                {
                    add_module(mp);
                }
            }
            for mp in libraries.all_module_paths() {
                if mp.segments().len() == parent.len() + 1
                    && mp.segments().starts_with(parent)
                    && mp != current
                {
                    add_module(mp);
                }
            }
        }
    }

    // Top-level workspace modules
    for mp in workspace.all_module_paths() {
        if mp.segments().len() == 1 {
            add_module(mp);
        }
    }

    // Library roots (top-level library paths)
    for mp in libraries.all_module_paths() {
        if mp.segments().len() == 1 {
            add_module(mp);
        }
    }

    results
}

/// Collect direct child module names of a given prefix.
///
/// For `core`, returns `["io", "ops", "string", ...]`.
pub fn child_modules(db: &Database, prefix: &ModulePath) -> Vec<String> {
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let libraries = db.get_input::<LoadedLibraries>(());
    let prefix_len = prefix.segments().len();

    let mut names = Vec::new();
    let mut seen = std::collections::HashSet::new();

    for mp in workspace
        .all_module_paths()
        .chain(libraries.all_module_paths())
    {
        if mp.segments().len() == prefix_len + 1 && mp.segments().starts_with(prefix.segments()) {
            if let Some(name) = mp.segments().last() {
                if seen.insert(name.clone()) {
                    names.push(name.clone());
                }
            }
        }
    }

    names
}

/// Collect exported names from a module (both workspace and library sources).
///
/// Returns `(name, DefTarget)` pairs for all exports of the module.
pub fn get_module_exports(db: &Database, module_path: &ModulePath) -> Vec<(String, DefTarget)> {
    use crate::queries::{exports::module_def_index, resolve::get_library_exports};

    let mut results = Vec::new();

    // Workspace exports
    let exports = module_def_index(db, module_path.clone());
    for (name, result) in exports {
        if let Ok(item) = result {
            let target = match item {
                crate::queries::exports::ExportedItem::Def(def_id) => DefTarget::Workspace(def_id),
                crate::queries::exports::ExportedItem::Local(_) => continue,
                crate::queries::exports::ExportedItem::ReExport(target) => target,
                crate::queries::exports::ExportedItem::Module(_) => continue,
            };
            results.push((name, target));
        }
    }

    // Library exports
    let libraries = db.get_input::<LoadedLibraries>(());
    for (name, target) in get_library_exports(&libraries, module_path) {
        results.push((name, target));
    }

    results
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
        Decl::Test(test) => find_ctx_in_expr(&test.body, srcmap, pos),
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

        Expr::NilCoalesce(nc) => find_ctx_in_expr(&nc.lhs, srcmap, pos)
            .or_else(|| find_ctx_in_expr(&nc.rhs, srcmap, pos)),

        Expr::FString(fstr) => fstr.parts.iter().find_map(|part| match part {
            FStringPart::Expr(expr) => find_ctx_in_expr(expr, srcmap, pos),
            FStringPart::Literal(_) => None,
        }),

        Expr::Paren(inner)
        | Expr::Some(inner)
        | Expr::DefaultValue(inner)
        | Expr::Unsafe(inner) => find_ctx_in_expr(inner, srcmap, pos),

        Expr::Boxed(boxed) => find_ctx_in_expr(&boxed.inner, srcmap, pos),

        Expr::BuiltinCall(bc) => find_ctx_in_expr(&bc.arg, srcmap, pos),

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

        Expr::New(_) => None,

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
        pathlib::{FilePath, ModulePath, Path},
        resolution::DefTarget,
        scope::ScopeEntry,
        span::Pos,
        ty::Ty,
    };

    use crate::{
        queries::{
            completion::{CompletionKind, completion_context},
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
        db.set_input::<CompilerOptions>(
            (),
            CompilerOptions {
                no_core: true,
                test_mode: false,
            },
        );
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );
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
        match &ctx.kind {
            CompletionKind::TypeMember(DefTarget::Workspace(def_id)) => {
                assert_eq!(
                    def_id.file, file_id,
                    "TypeMember should reference a def in the same file"
                );
            }
            other => panic!("Point:: should be TypeMember(Workspace), got: {:?}", other),
        }
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
        db.set_input::<CompilerOptions>(
            (),
            CompilerOptions {
                no_core: true,
                test_mode: false,
            },
        );

        let source_main = "import utils\nfn main() {\n    utils::\n}";
        let source_utils = "fn helper() {}";
        FileSource::new(&db, file_main, source_main.to_string());
        FileMetadata::new(
            &db,
            file_main,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );
        FileSource::new(&db, file_utils, source_utils.to_string());
        FileMetadata::new(
            &db,
            file_utils,
            FilePath::from("utils.ray"),
            ModulePath::from("utils"),
        );

        let pos = pos_after(source_main, "utils::");
        let ctx = completion_context(&db, file_main, pos)
            .expect("should return completion after module::");
        match &ctx.kind {
            CompletionKind::ModuleMember(module_path) => {
                assert_eq!(
                    module_path.to_string(),
                    "utils",
                    "ModuleMember should reference the utils module"
                );
            }
            other => panic!("utils:: should be ModuleMember, got: {:?}", other),
        }
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
        // Receiver is `x.y` where `y` doesn't exist on Foo — type is an unresolved
        // inference variable. We still get Member kind thanks to parser error recovery.
        let receiver = ctx
            .receiver_type
            .expect("chained dot should still have a receiver type (unresolved)");
        assert!(
            matches!(&receiver, Ty::Var(_)),
            "receiver of x.y. (nonexistent field) should be an unresolved type var, got: {:?}",
            receiver
        );
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
        // `p` is assigned from broken code — its type is an unresolved inference variable.
        // The important thing is we still get Member kind for dot completion.
        let receiver = ctx
            .receiver_type
            .expect("p. should still have a receiver type (unresolved)");
        assert!(
            matches!(&receiver, Ty::Var(_)),
            "receiver of p. (from broken assignment) should be an unresolved type var, got: {:?}",
            receiver
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
        match &ctx.kind {
            CompletionKind::TypeMember(DefTarget::Workspace(def_id)) => {
                assert_eq!(
                    def_id.file, file_id,
                    "TypeMember should reference a def in the same file"
                );
            }
            other => panic!(
                "Point::cr should be TypeMember(Workspace), got: {:?}",
                other
            ),
        }
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
        db.set_input::<CompilerOptions>(
            (),
            CompilerOptions {
                no_core: true,
                test_mode: false,
            },
        );

        let source_main = "import utils\nfn main() { utils::hel }";
        let source_utils = "fn helper() {}";
        FileSource::new(&db, file_main, source_main.to_string());
        FileMetadata::new(
            &db,
            file_main,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );
        FileSource::new(&db, file_utils, source_utils.to_string());
        FileMetadata::new(
            &db,
            file_utils,
            FilePath::from("utils.ray"),
            ModulePath::from("utils"),
        );

        let pos = pos_after(source_main, "utils::hel");
        let ctx = completion_context(&db, file_main, pos)
            .expect("should return completion for partial module access");
        match &ctx.kind {
            CompletionKind::ModuleMember(module_path) => {
                assert_eq!(
                    module_path.to_string(),
                    "utils",
                    "ModuleMember should reference the utils module"
                );
            }
            other => panic!("utils::hel should be ModuleMember, got: {:?}", other),
        }
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
        assert_eq!(ctx.kind, CompletionKind::Scope);
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

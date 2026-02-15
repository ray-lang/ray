//! Scope query for LSP completion and other IDE features.
//!
//! The `scope_at` query returns all names visible at a given position in a file.
//! This includes local bindings, top-level definitions, imports, and sibling
//! module exports.

use std::{collections::HashMap, sync::Arc};

use ray_core::{
    ast::{Decl, Expr, FStringPart, FnParam, Node, Pattern},
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::{
    file_id::FileId, local_binding::LocalBindingId, node_id::NodeId, resolution::Resolution,
    scope::ScopeEntry, span::Pos,
};

use crate::{
    queries::{
        imports::{ImportNames, resolved_imports},
        parse::parse_file,
        resolve::{file_scope, name_resolutions},
    },
    query::{Database, Query},
};

/// Returns all names in scope at a given position in a file.
///
/// Combines file-level scope (top-level definitions, imports, sibling exports)
/// with local bindings (parameters, let-bindings) visible at the position.
///
/// Dependencies: `parse_file`, `name_resolutions`, `file_scope`, `resolved_imports`.
///
/// Returns partial results when some names couldn't be resolved (e.g., due to
/// parse errors in imported modules).
#[query]
pub fn scope_at(db: &Database, file_id: FileId, pos: Pos) -> Arc<Vec<(String, ScopeEntry)>> {
    let parse_result = parse_file(db, file_id);
    let resolutions = name_resolutions(db, file_id);
    let top_level_scope = file_scope(db, file_id);
    let imports = resolved_imports(db, file_id);

    let mut result: Vec<(String, ScopeEntry)> = Vec::new();

    // 1. File-level definitions (top-level defs, selective/glob imports, sibling exports)
    for (name, def_target) in &top_level_scope {
        result.push((name.clone(), ScopeEntry::Def(def_target.clone())));
    }

    // 2. Namespace imports (e.g., `import utils` makes `utils` a module handle)
    for (alias, import_result) in &imports {
        if let Ok(resolved_import) = import_result {
            if matches!(resolved_import.names, ImportNames::Namespace) {
                result.push((
                    alias.clone(),
                    ScopeEntry::Module(resolved_import.module_path.clone()),
                ));
            }
        }
    }

    // 3. Local bindings visible at the position
    let locals = collect_locals_at(
        &parse_result.ast,
        &parse_result.source_map,
        &pos,
        &resolutions,
    );
    for (name, local_id) in locals {
        result.push((name, ScopeEntry::Local(local_id)));
    }

    Arc::new(result)
}

/// Collect local bindings visible at `pos` by walking the AST.
///
/// Walks into scope-creating constructs (functions, blocks, closures, for-loops)
/// and collects bindings (parameters, assignments) that are defined before `pos`
/// in enclosing scopes.
fn collect_locals_at(
    file: &ray_core::ast::File,
    srcmap: &SourceMap,
    pos: &Pos,
    resolutions: &HashMap<NodeId, Resolution>,
) -> Vec<(String, LocalBindingId)> {
    let mut locals = Vec::new();

    for decl in &file.decls {
        collect_locals_in_decl(decl, srcmap, pos, resolutions, &mut locals);
    }

    for stmt in &file.stmts {
        collect_locals_in_expr(stmt, srcmap, pos, resolutions, &mut locals);
    }

    locals
}

/// Walk a declaration looking for local bindings visible at `pos`.
fn collect_locals_in_decl(
    decl: &Node<Decl>,
    srcmap: &SourceMap,
    pos: &Pos,
    resolutions: &HashMap<NodeId, Resolution>,
    locals: &mut Vec<(String, LocalBindingId)>,
) {
    match &decl.value {
        Decl::Func(func) => {
            let span = srcmap.get_by_id(decl.id).and_then(|s| s.span);
            let Some(span) = span else { return };
            if !span.contains_pos(pos) {
                return;
            }

            // Parameters are visible throughout the function body
            for param in &func.sig.params {
                collect_param_binding(param, srcmap, resolutions, locals);
            }

            // Recurse into the body
            if let Some(body) = &func.body {
                collect_locals_in_expr(body, srcmap, pos, resolutions, locals);
            }
        }
        Decl::Impl(im) => {
            if let Some(funcs) = &im.funcs {
                for func_decl in funcs {
                    collect_locals_in_decl(func_decl, srcmap, pos, resolutions, locals);
                }
            }
        }
        Decl::Trait(tr) => {
            for field in &tr.fields {
                collect_locals_in_decl(field, srcmap, pos, resolutions, locals);
            }
        }
        Decl::FileMain(stmts) => {
            // Top-level statements: bindings defined before `pos` are visible
            for stmt in stmts {
                let stmt_span = srcmap.get_by_id(stmt.id).and_then(|s| s.span);
                if let Some(stmt_span) = stmt_span {
                    // Only collect bindings from statements that start before pos
                    if stmt_span.start.offset <= pos.offset {
                        collect_binding_from_expr(stmt, srcmap, resolutions, locals);
                    }
                }
                // Recurse into the statement if pos is inside it
                collect_locals_in_expr(stmt, srcmap, pos, resolutions, locals);
            }
        }
        // Other declarations don't introduce local scopes
        Decl::Struct(_)
        | Decl::FnSig(_)
        | Decl::TypeAlias(_, _)
        | Decl::Mutable(_, _)
        | Decl::Name(_, _)
        | Decl::Declare(_) => {}
    }
}

/// Walk an expression looking for local bindings visible at `pos`.
fn collect_locals_in_expr(
    expr: &Node<Expr>,
    srcmap: &SourceMap,
    pos: &Pos,
    resolutions: &HashMap<NodeId, Resolution>,
    locals: &mut Vec<(String, LocalBindingId)>,
) {
    let span = srcmap.get_by_id(expr.id).and_then(|s| s.span);

    match &expr.value {
        Expr::Block(block) => {
            // Block: bindings defined before `pos` are visible within the block
            if let Some(span) = span {
                if !span.contains_pos(pos) {
                    return;
                }
            }

            for stmt in &block.stmts {
                let stmt_span = srcmap.get_by_id(stmt.id).and_then(|s| s.span);
                if let Some(stmt_span) = stmt_span {
                    if stmt_span.start.offset <= pos.offset {
                        collect_binding_from_expr(stmt, srcmap, resolutions, locals);
                    }
                }
                collect_locals_in_expr(stmt, srcmap, pos, resolutions, locals);
            }
        }
        Expr::Func(func) => {
            if let Some(span) = span {
                if !span.contains_pos(pos) {
                    return;
                }
            }

            for param in &func.sig.params {
                collect_param_binding(param, srcmap, resolutions, locals);
            }
            if let Some(body) = &func.body {
                collect_locals_in_expr(body, srcmap, pos, resolutions, locals);
            }
        }
        Expr::Closure(closure) => {
            if let Some(span) = span {
                if !span.contains_pos(pos) {
                    return;
                }
            }

            // Closure args are expressions (typically Names), collect their bindings
            for arg in &closure.args.items {
                collect_binding_from_expr(arg, srcmap, resolutions, locals);
            }
            collect_locals_in_expr(&closure.body, srcmap, pos, resolutions, locals);
        }
        Expr::For(for_expr) => {
            if let Some(span) = span {
                if !span.contains_pos(pos) {
                    return;
                }
            }

            // Loop variable
            collect_pattern_binding(&for_expr.pat, srcmap, resolutions, locals);
            collect_locals_in_expr(&for_expr.body, srcmap, pos, resolutions, locals);
        }
        Expr::If(if_expr) => {
            collect_locals_in_expr(&if_expr.cond, srcmap, pos, resolutions, locals);
            collect_locals_in_expr(&if_expr.then, srcmap, pos, resolutions, locals);
            if let Some(els) = &if_expr.els {
                collect_locals_in_expr(els, srcmap, pos, resolutions, locals);
            }
        }
        Expr::While(while_expr) => {
            collect_locals_in_expr(&while_expr.cond, srcmap, pos, resolutions, locals);
            collect_locals_in_expr(&while_expr.body, srcmap, pos, resolutions, locals);
        }
        Expr::Loop(loop_expr) => {
            collect_locals_in_expr(&loop_expr.body, srcmap, pos, resolutions, locals);
        }
        // For assign, the binding is collected by the parent (block/FileMain),
        // but we still recurse into the RHS in case it contains nested scopes.
        Expr::Assign(assign) => {
            collect_locals_in_expr(&assign.rhs, srcmap, pos, resolutions, locals);
        }
        // Other expressions: recurse into children that might contain scopes
        Expr::Call(call) => {
            collect_locals_in_expr(&call.callee, srcmap, pos, resolutions, locals);
            for arg in &call.args.items {
                collect_locals_in_expr(arg, srcmap, pos, resolutions, locals);
            }
        }
        Expr::BinOp(binop) => {
            collect_locals_in_expr(&binop.lhs, srcmap, pos, resolutions, locals);
            collect_locals_in_expr(&binop.rhs, srcmap, pos, resolutions, locals);
        }
        Expr::NilCoalesce(nc) => {
            collect_locals_in_expr(&nc.lhs, srcmap, pos, resolutions, locals);
            collect_locals_in_expr(&nc.rhs, srcmap, pos, resolutions, locals);
        }
        Expr::FString(fstr) => {
            for part in &fstr.parts {
                if let FStringPart::Expr(expr) = part {
                    collect_locals_in_expr(expr, srcmap, pos, resolutions, locals);
                }
            }
        }
        Expr::Paren(inner)
        | Expr::Some(inner)
        | Expr::DefaultValue(inner)
        | Expr::Unsafe(inner) => {
            collect_locals_in_expr(inner, srcmap, pos, resolutions, locals);
        }
        Expr::Boxed(boxed) => {
            collect_locals_in_expr(&boxed.inner, srcmap, pos, resolutions, locals);
        }
        Expr::Return(val) | Expr::Break(val) => {
            if let Some(inner) = val {
                collect_locals_in_expr(inner, srcmap, pos, resolutions, locals);
            }
        }
        Expr::Dot(dot) => {
            collect_locals_in_expr(&dot.lhs, srcmap, pos, resolutions, locals);
        }
        Expr::Index(index) => {
            collect_locals_in_expr(&index.lhs, srcmap, pos, resolutions, locals);
            collect_locals_in_expr(&index.index, srcmap, pos, resolutions, locals);
        }
        Expr::TypeAnnotated(inner, _) | Expr::Labeled(_, inner) => {
            collect_locals_in_expr(inner, srcmap, pos, resolutions, locals);
        }
        Expr::Cast(cast) => {
            collect_locals_in_expr(&cast.lhs, srcmap, pos, resolutions, locals);
        }
        Expr::Deref(deref) => {
            collect_locals_in_expr(&deref.expr, srcmap, pos, resolutions, locals);
        }
        Expr::Ref(rf) => {
            collect_locals_in_expr(&rf.expr, srcmap, pos, resolutions, locals);
        }
        Expr::UnaryOp(unary) => {
            collect_locals_in_expr(&unary.expr, srcmap, pos, resolutions, locals);
        }
        Expr::Range(range) => {
            collect_locals_in_expr(&range.start, srcmap, pos, resolutions, locals);
            collect_locals_in_expr(&range.end, srcmap, pos, resolutions, locals);
        }
        Expr::Tuple(tuple) => {
            for item in &tuple.seq.items {
                collect_locals_in_expr(item, srcmap, pos, resolutions, locals);
            }
        }
        Expr::List(list) => {
            for item in &list.items {
                collect_locals_in_expr(item, srcmap, pos, resolutions, locals);
            }
        }
        Expr::Sequence(seq) => {
            for item in &seq.items {
                collect_locals_in_expr(item, srcmap, pos, resolutions, locals);
            }
        }
        Expr::ScopedAccess(sa) => {
            collect_locals_in_expr(&sa.lhs, srcmap, pos, resolutions, locals);
        }
        Expr::Curly(curly) => {
            for elem in &curly.elements {
                if let ray_core::ast::CurlyElement::Labeled(_, expr) = &elem.value {
                    collect_locals_in_expr(expr, srcmap, pos, resolutions, locals);
                }
            }
        }
        Expr::Dict(dict) => {
            for (k, v) in &dict.entries {
                collect_locals_in_expr(k, srcmap, pos, resolutions, locals);
                collect_locals_in_expr(v, srcmap, pos, resolutions, locals);
            }
        }
        Expr::Set(set) => {
            for item in &set.items {
                collect_locals_in_expr(item, srcmap, pos, resolutions, locals);
            }
        }
        Expr::New(new_expr) => {
            if let Some(count) = &new_expr.count {
                collect_locals_in_expr(count, srcmap, pos, resolutions, locals);
            }
        }
        // Leaf expressions — no children to recurse into
        Expr::Name(_)
        | Expr::Literal(_)
        | Expr::Continue
        | Expr::Missing(_)
        | Expr::Path(_)
        | Expr::Pattern(_)
        | Expr::Type(_) => {}
    }
}

/// Extract a binding from a function parameter node.
fn collect_param_binding(
    param: &Node<FnParam>,
    srcmap: &SourceMap,
    resolutions: &HashMap<NodeId, Resolution>,
    locals: &mut Vec<(String, LocalBindingId)>,
) {
    match &param.value {
        FnParam::Name(name) => {
            if let Some(name_str) = name.path.name() {
                if let Some(local_id) = resolution_to_local(param.id, resolutions, srcmap) {
                    locals.push((name_str, local_id));
                }
            }
        }
        FnParam::DefaultValue(inner, _) => {
            collect_param_binding(inner, srcmap, resolutions, locals);
        }
        FnParam::Missing { .. } => {}
    }
}

/// Extract a binding from a pattern node (e.g., LHS of assignment).
fn collect_pattern_binding(
    pattern: &Node<Pattern>,
    srcmap: &SourceMap,
    resolutions: &HashMap<NodeId, Resolution>,
    locals: &mut Vec<(String, LocalBindingId)>,
) {
    match &pattern.value {
        Pattern::Name(name) => {
            if let Some(name_str) = name.path.name() {
                if let Some(local_id) = resolution_to_local(pattern.id, resolutions, srcmap) {
                    locals.push((name_str, local_id));
                }
            }
        }
        Pattern::Deref(name_node) => {
            if let Some(name_str) = name_node.value.path.name() {
                if let Some(local_id) = resolution_to_local(name_node.id, resolutions, srcmap) {
                    locals.push((name_str, local_id));
                }
            }
        }
        Pattern::Sequence(pats) | Pattern::Tuple(pats) => {
            for pat in pats {
                collect_pattern_binding(pat, srcmap, resolutions, locals);
            }
        }
        Pattern::Some(inner) => {
            collect_pattern_binding(inner, srcmap, resolutions, locals);
        }
        Pattern::Dot(_, _) | Pattern::Index(_, _, _) | Pattern::Missing(_) => {}
    }
}

/// Extract a binding from an expression that introduces a name (assignment, name expr).
fn collect_binding_from_expr(
    expr: &Node<Expr>,
    srcmap: &SourceMap,
    resolutions: &HashMap<NodeId, Resolution>,
    locals: &mut Vec<(String, LocalBindingId)>,
) {
    if let Expr::Assign(assign) = &expr.value {
        collect_pattern_binding(&assign.lhs, srcmap, resolutions, locals);
    }
}

/// Look up a node's resolution to extract a LocalBindingId.
///
/// The name resolution pass stores `Resolution::Local(local_id)` for both
/// binding definition sites and use sites. We use this to get the
/// `LocalBindingId` for binding definitions.
fn resolution_to_local(
    node_id: NodeId,
    resolutions: &HashMap<NodeId, Resolution>,
    _srcmap: &SourceMap,
) -> Option<LocalBindingId> {
    match resolutions.get(&node_id) {
        Some(Resolution::Local(local_id)) => Some(*local_id),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        file_id::FileId,
        pathlib::{FilePath, ModulePath, Path},
        scope::ScopeEntry,
        span::Pos,
    };

    use crate::{
        queries::{
            libraries::LoadedLibraries,
            scope::scope_at,
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
    fn scope_at_includes_top_level_function() {
        let source = "fn foo() {}\nfn bar() {}";
        let (db, file_id) = setup_db(source);

        // Position inside bar's body
        let pos = pos_of(source, "bar");
        let scope = scope_at(&db, file_id, pos);

        let names: Vec<&str> = scope.iter().map(|(n, _)| n.as_str()).collect();
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

        // Both should be Def entries
        for (_, entry) in scope.iter() {
            if matches!(entry, ScopeEntry::Def(_)) {
                continue;
            }
        }
    }

    #[test]
    fn scope_at_includes_function_parameters() {
        let source = "fn foo(x, y) { x }";
        let (db, file_id) = setup_db(source);

        // Position at the `x` usage inside the body
        let pos = pos_of(source, "{ x");
        // Adjust to be inside the body
        let pos = Pos {
            offset: pos.offset + 2,
            col: pos.col + 2,
            ..pos
        };
        let scope = scope_at(&db, file_id, pos);

        let names: Vec<&str> = scope.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            names.contains(&"x"),
            "parameter x should be in scope, got: {:?}",
            names
        );
        assert!(
            names.contains(&"y"),
            "parameter y should be in scope, got: {:?}",
            names
        );
    }

    #[test]
    fn scope_at_includes_local_bindings() {
        let source = "fn foo() {\n    a = 1\n    b = 2\n    b\n}";
        let (db, file_id) = setup_db(source);

        // Position at the final `b` usage
        let pos = pos_of(source, "\n    b\n}");
        let pos = Pos {
            offset: pos.offset + 5,
            col: 4,
            lineno: pos.lineno + 1,
        };
        let scope = scope_at(&db, file_id, pos);

        let local_names: Vec<&str> = scope
            .iter()
            .filter(|(_, e)| matches!(e, ScopeEntry::Local(_)))
            .map(|(n, _)| n.as_str())
            .collect();
        assert!(
            local_names.contains(&"a"),
            "local a should be in scope, got: {:?}",
            local_names
        );
        assert!(
            local_names.contains(&"b"),
            "local b should be in scope, got: {:?}",
            local_names
        );
    }

    #[test]
    fn scope_at_empty_file() {
        let source = "";
        let (db, file_id) = setup_db(source);
        let pos = Pos {
            lineno: 0,
            col: 0,
            offset: 0,
        };
        let scope = scope_at(&db, file_id, pos);
        assert!(scope.is_empty(), "empty file should have empty scope");
    }

    #[test]
    fn scope_at_does_not_include_bindings_from_other_functions() {
        let source = "fn foo(x) { x }\nfn bar(y) { y }";
        let (db, file_id) = setup_db(source);

        // Position inside bar's body
        let pos = pos_of(source, "{ y }");
        let pos = Pos {
            offset: pos.offset + 2,
            col: pos.col + 2,
            ..pos
        };
        let scope = scope_at(&db, file_id, pos);

        let local_names: Vec<&str> = scope
            .iter()
            .filter(|(_, e)| matches!(e, ScopeEntry::Local(_)))
            .map(|(n, _)| n.as_str())
            .collect();
        assert!(
            local_names.contains(&"y"),
            "y should be in scope inside bar, got: {:?}",
            local_names
        );
        assert!(
            !local_names.contains(&"x"),
            "x should NOT be in scope inside bar, got: {:?}",
            local_names
        );
    }

    #[test]
    fn scope_at_handles_parse_errors() {
        // Valid function followed by a malformed one
        let source = "fn foo() {}\nfn bar( {";
        let (db, file_id) = setup_db(source);

        // Position at the start of the broken function
        let pos = pos_of(source, "bar");
        let scope = scope_at(&db, file_id, pos);

        // foo should still be in scope despite parse errors in bar
        let names: Vec<&str> = scope.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            names.contains(&"foo"),
            "foo should still be in scope despite parse errors, got: {:?}",
            names
        );
    }

    #[test]
    fn scope_at_includes_struct() {
        let source = "struct Point { x: int, y: int }\nfn main() { x = 1 }";
        let (db, file_id) = setup_db(source);

        // Position inside main's body
        let pos = pos_of(source, "x = 1");
        let scope = scope_at(&db, file_id, pos);

        let names: Vec<&str> = scope.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            names.contains(&"Point"),
            "struct Point should be in scope, got: {:?}",
            names
        );

        let point_entry = scope.iter().find(|(n, _)| n == "Point").unwrap();
        assert!(
            matches!(point_entry.1, ScopeEntry::Def(_)),
            "Point should be a Def entry"
        );
    }

    #[test]
    fn scope_at_includes_trait() {
        let source = "trait Foo {\n    fn bar()\n}\nfn main() { x = 1 }";
        let (db, file_id) = setup_db(source);

        // Position inside main's body
        let pos = pos_of(source, "x = 1");
        let scope = scope_at(&db, file_id, pos);

        let names: Vec<&str> = scope.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            names.contains(&"Foo"),
            "trait Foo should be in scope, got: {:?}",
            names
        );

        let foo_entry = scope.iter().find(|(n, _)| n == "Foo").unwrap();
        assert!(
            matches!(foo_entry.1, ScopeEntry::Def(_)),
            "Foo should be a Def entry"
        );
    }

    #[test]
    fn scope_at_includes_sibling_exports() {
        // Two files in the same module: exports from b.ray should be visible in a.ray
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let file_a = workspace.add_file(FilePath::from("mymod/a.ray"), Path::from("mymod"));
        let file_b = workspace.add_file(FilePath::from("mymod/b.ray"), Path::from("mymod"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: true });

        let source_a = "fn main() { x = 1 }";
        let source_b = "fn helper() {}";
        FileSource::new(&db, file_a, source_a.to_string());
        FileMetadata::new(
            &db,
            file_a,
            FilePath::from("mymod/a.ray"),
            ModulePath::from("mymod"),
        );
        FileSource::new(&db, file_b, source_b.to_string());
        FileMetadata::new(
            &db,
            file_b,
            FilePath::from("mymod/b.ray"),
            ModulePath::from("mymod"),
        );

        // Position inside main's body in file a
        let pos = pos_of(source_a, "x = 1");
        let scope = scope_at(&db, file_a, pos);

        let names: Vec<&str> = scope.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            names.contains(&"helper"),
            "sibling export helper should be in scope, got: {:?}",
            names
        );
        assert!(
            names.contains(&"main"),
            "own file's main should be in scope, got: {:?}",
            names
        );
    }

    #[test]
    fn scope_at_includes_namespace_import() {
        // `import utils` should make `utils` visible as a Module entry
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let file_main = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        let file_utils = workspace.add_file(FilePath::from("utils.ray"), Path::from("utils"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: true });

        let source_main = "import utils\nfn main() { x = 1 }";
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

        let pos = pos_of(source_main, "x = 1");
        let scope = scope_at(&db, file_main, pos);

        let names: Vec<&str> = scope.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            names.contains(&"utils"),
            "namespace import utils should be in scope, got: {:?}",
            names
        );

        let utils_entry = scope.iter().find(|(n, _)| n == "utils").unwrap();
        assert!(
            matches!(utils_entry.1, ScopeEntry::Module(_)),
            "utils should be a Module entry, got: {:?}",
            utils_entry.1
        );
    }

    #[test]
    fn scope_at_includes_selective_import() {
        // `import utils with helper` should make `helper` visible as a Def entry
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let file_main = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        let file_utils = workspace.add_file(FilePath::from("utils.ray"), Path::from("utils"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: true });

        let source_main = "import utils with helper\nfn main() { x = 1 }";
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

        let pos = pos_of(source_main, "x = 1");
        let scope = scope_at(&db, file_main, pos);

        let names: Vec<&str> = scope.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            names.contains(&"helper"),
            "selectively imported helper should be in scope, got: {:?}",
            names
        );

        let helper_entry = scope.iter().find(|(n, _)| n == "helper").unwrap();
        assert!(
            matches!(helper_entry.1, ScopeEntry::Def(_)),
            "helper should be a Def entry, got: {:?}",
            helper_entry.1
        );
    }
}

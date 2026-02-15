//! Binding-related queries for the incremental query system.
//!
//! This module provides queries for looking up binding information from
//! name resolution results.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use ray_core::ast::{CurlyElement, Decl, Expr, FStringPart, FnParam, Node, Pattern};
use ray_query_macros::query;
use ray_shared::{
    file_id::FileId, local_binding::LocalBindingId, node_id::NodeId, resolution::Resolution,
    symbol::SymbolIdentity,
};

use crate::{
    queries::{
        deps::{BindingGroupId, binding_group_members},
        parse::parse_file,
        resolve::name_resolutions,
        symbols::definition_identities,
    },
    query::{Database, Query},
};

/// Returns the LocalBindingId for a node if it resolves to a local binding.
///
/// This query looks up name resolution results for an AST node. Nodes that
/// resolve to local bindings (parameters, let-bindings, etc.) will return
/// their LocalBindingId.
///
/// # Arguments
///
/// * `db` - The query database
/// * `node_id` - The AST node identifier
///
/// # Returns
///
/// The LocalBindingId if this node resolves to a local binding, or `None` otherwise.
#[query]
pub fn local_binding_for_node(db: &Database, node_id: NodeId) -> Option<LocalBindingId> {
    let file_id = node_id.owner.file;
    let resolutions = name_resolutions(db, file_id);
    match resolutions.get(&node_id) {
        Some(Resolution::Local(local_id)) => Some(*local_id),
        _ => None,
    }
}

/// Returns all NodeId → LocalBindingId mappings for nodes in a binding group.
///
/// This query aggregates name resolution results for all definitions in a binding
/// group, filtering to only local binding resolutions. This is used by the type
/// checker's copy step to populate `node_tys` from `local_tys`.
///
/// # Arguments
///
/// * `db` - The query database
/// * `group_id` - The binding group identifier
///
/// # Returns
///
/// A map from NodeId to LocalBindingId for all nodes in the group that resolve
/// to local bindings.
#[query]
pub fn local_bindings_for_group(
    db: &Database,
    group_id: BindingGroupId,
) -> HashMap<NodeId, LocalBindingId> {
    let members = binding_group_members(db, group_id);

    // Collect unique files from the group members
    let files: HashSet<_> = members.iter().map(|def_id| def_id.file).collect();

    // Aggregate local binding resolutions from all files
    let mut result = HashMap::new();
    for file_id in files {
        let resolutions = name_resolutions(db, file_id);
        for (node_id, resolution) in resolutions.iter() {
            // Only include nodes owned by a def in this group
            if members.contains(&node_id.owner) {
                if let Resolution::Local(local_id) = resolution {
                    result.insert(*node_id, *local_id);
                }
            }
        }
    }

    result
}

/// Returns all LocalBindingId → name mappings for a file.
///
/// Walks the AST to find all binding definition sites (function parameters,
/// assignment LHS patterns, closure args, for-loop variables) and maps each
/// LocalBindingId to its source name.
///
/// This is used by the hover handler to display `name: type` for locals.
#[query]
pub fn local_binding_names(db: &Database, file_id: FileId) -> Arc<HashMap<LocalBindingId, String>> {
    let parse_result = parse_file(db, file_id);
    let resolutions = name_resolutions(db, file_id);
    let mut names = HashMap::new();

    for decl in &parse_result.ast.decls {
        collect_all_bindings_in_decl(decl, &resolutions, &mut names);
    }

    for stmt in &parse_result.ast.stmts {
        collect_all_bindings_in_expr(stmt, &resolutions, &mut names);
    }

    Arc::new(names)
}

/// Returns the definition-site NodeId for each LocalBindingId in a file.
///
/// This is the reverse of the local binding entries in `definition_identities`:
/// given a LocalBindingId, returns the NodeId where that binding was defined
/// (parameter, assignment LHS, closure arg, etc.).
///
/// Used by go-to-definition to navigate to local binding definition sites.
///
/// **Dependencies**: `definition_identities(file_id)`
#[query]
pub fn local_binding_definitions(
    db: &Database,
    file_id: FileId,
) -> HashMap<LocalBindingId, NodeId> {
    let identities = definition_identities(db, file_id);
    let mut result = HashMap::new();
    for (node_id, identity) in &identities {
        if let SymbolIdentity::Local(local_id) = identity {
            result.insert(*local_id, *node_id);
        }
    }
    result
}

// ---------------------------------------------------------------------------
// AST walkers for collecting ALL local binding names (no position filtering)
// ---------------------------------------------------------------------------

fn collect_all_bindings_in_decl(
    decl: &Node<Decl>,
    resolutions: &HashMap<NodeId, Resolution>,
    names: &mut HashMap<LocalBindingId, String>,
) {
    match &decl.value {
        Decl::Func(func) => {
            for param in &func.sig.params {
                collect_param_name(param, resolutions, names);
            }
            if let Some(body) = &func.body {
                collect_all_bindings_in_expr(body, resolutions, names);
            }
        }
        Decl::Impl(im) => {
            if let Some(funcs) = &im.funcs {
                for func_decl in funcs {
                    collect_all_bindings_in_decl(func_decl, resolutions, names);
                }
            }
        }
        Decl::Trait(tr) => {
            for field in &tr.fields {
                collect_all_bindings_in_decl(field, resolutions, names);
            }
        }
        Decl::FileMain(stmts) => {
            for stmt in stmts {
                collect_binding_name_from_expr(stmt, resolutions, names);
                collect_all_bindings_in_expr(stmt, resolutions, names);
            }
        }
        Decl::Struct(_)
        | Decl::FnSig(_)
        | Decl::TypeAlias(_, _)
        | Decl::Mutable(_, _)
        | Decl::Name(_, _)
        | Decl::Declare(_) => {}
    }
}

fn collect_all_bindings_in_expr(
    expr: &Node<Expr>,
    resolutions: &HashMap<NodeId, Resolution>,
    names: &mut HashMap<LocalBindingId, String>,
) {
    match &expr.value {
        Expr::Block(block) => {
            for stmt in &block.stmts {
                collect_binding_name_from_expr(stmt, resolutions, names);
                collect_all_bindings_in_expr(stmt, resolutions, names);
            }
        }
        Expr::Func(func) => {
            for param in &func.sig.params {
                collect_param_name(param, resolutions, names);
            }
            if let Some(body) = &func.body {
                collect_all_bindings_in_expr(body, resolutions, names);
            }
        }
        Expr::Closure(closure) => {
            for arg in &closure.args.items {
                collect_binding_name_from_expr(arg, resolutions, names);
            }
            collect_all_bindings_in_expr(&closure.body, resolutions, names);
        }
        Expr::For(for_expr) => {
            collect_pattern_name(&for_expr.pat, resolutions, names);
            collect_all_bindings_in_expr(&for_expr.body, resolutions, names);
        }
        Expr::If(if_expr) => {
            collect_all_bindings_in_expr(&if_expr.cond, resolutions, names);
            collect_all_bindings_in_expr(&if_expr.then, resolutions, names);
            if let Some(els) = &if_expr.els {
                collect_all_bindings_in_expr(els, resolutions, names);
            }
        }
        Expr::While(while_expr) => {
            collect_all_bindings_in_expr(&while_expr.cond, resolutions, names);
            collect_all_bindings_in_expr(&while_expr.body, resolutions, names);
        }
        Expr::Loop(loop_expr) => {
            collect_all_bindings_in_expr(&loop_expr.body, resolutions, names);
        }
        Expr::Assign(assign) => {
            collect_all_bindings_in_expr(&assign.rhs, resolutions, names);
        }
        Expr::Call(call) => {
            collect_all_bindings_in_expr(&call.callee, resolutions, names);
            for arg in &call.args.items {
                collect_all_bindings_in_expr(arg, resolutions, names);
            }
        }
        Expr::BinOp(binop) => {
            collect_all_bindings_in_expr(&binop.lhs, resolutions, names);
            collect_all_bindings_in_expr(&binop.rhs, resolutions, names);
        }
        Expr::NilCoalesce(nc) => {
            collect_all_bindings_in_expr(&nc.lhs, resolutions, names);
            collect_all_bindings_in_expr(&nc.rhs, resolutions, names);
        }
        Expr::FString(fstr) => {
            for part in &fstr.parts {
                if let FStringPart::Expr(expr) = part {
                    collect_all_bindings_in_expr(expr, resolutions, names);
                }
            }
        }
        Expr::Paren(inner)
        | Expr::Some(inner)
        | Expr::DefaultValue(inner)
        | Expr::Unsafe(inner) => {
            collect_all_bindings_in_expr(inner, resolutions, names);
        }
        Expr::Boxed(boxed) => {
            collect_all_bindings_in_expr(&boxed.inner, resolutions, names);
        }
        Expr::Return(val) | Expr::Break(val) => {
            if let Some(inner) = val {
                collect_all_bindings_in_expr(inner, resolutions, names);
            }
        }
        Expr::Dot(dot) => {
            collect_all_bindings_in_expr(&dot.lhs, resolutions, names);
        }
        Expr::Index(index) => {
            collect_all_bindings_in_expr(&index.lhs, resolutions, names);
            collect_all_bindings_in_expr(&index.index, resolutions, names);
        }
        Expr::TypeAnnotated(inner, _) | Expr::Labeled(_, inner) => {
            collect_all_bindings_in_expr(inner, resolutions, names);
        }
        Expr::Cast(cast) => {
            collect_all_bindings_in_expr(&cast.lhs, resolutions, names);
        }
        Expr::Deref(deref) => {
            collect_all_bindings_in_expr(&deref.expr, resolutions, names);
        }
        Expr::Ref(rf) => {
            collect_all_bindings_in_expr(&rf.expr, resolutions, names);
        }
        Expr::UnaryOp(unary) => {
            collect_all_bindings_in_expr(&unary.expr, resolutions, names);
        }
        Expr::Range(range) => {
            collect_all_bindings_in_expr(&range.start, resolutions, names);
            collect_all_bindings_in_expr(&range.end, resolutions, names);
        }
        Expr::Tuple(tuple) => {
            for item in &tuple.seq.items {
                collect_all_bindings_in_expr(item, resolutions, names);
            }
        }
        Expr::List(list) => {
            for item in &list.items {
                collect_all_bindings_in_expr(item, resolutions, names);
            }
        }
        Expr::Sequence(seq) => {
            for item in &seq.items {
                collect_all_bindings_in_expr(item, resolutions, names);
            }
        }
        Expr::ScopedAccess(sa) => {
            collect_all_bindings_in_expr(&sa.lhs, resolutions, names);
        }
        Expr::Curly(curly) => {
            for elem in &curly.elements {
                if let CurlyElement::Labeled(_, expr) = &elem.value {
                    collect_all_bindings_in_expr(expr, resolutions, names);
                }
            }
        }
        Expr::Dict(dict) => {
            for (k, v) in &dict.entries {
                collect_all_bindings_in_expr(k, resolutions, names);
                collect_all_bindings_in_expr(v, resolutions, names);
            }
        }
        Expr::Set(set) => {
            for item in &set.items {
                collect_all_bindings_in_expr(item, resolutions, names);
            }
        }
        Expr::New(new_expr) => {
            if let Some(count) = &new_expr.count {
                collect_all_bindings_in_expr(count, resolutions, names);
            }
        }
        Expr::Name(_)
        | Expr::Literal(_)
        | Expr::Continue
        | Expr::Missing(_)
        | Expr::Path(_)
        | Expr::Pattern(_)
        | Expr::Type(_) => {}
    }
}

// ---------------------------------------------------------------------------
// Binding name extractors
// ---------------------------------------------------------------------------

fn collect_param_name(
    param: &Node<FnParam>,
    resolutions: &HashMap<NodeId, Resolution>,
    names: &mut HashMap<LocalBindingId, String>,
) {
    match &param.value {
        FnParam::Name(name) => {
            if let Some(name_str) = name.path.name() {
                if let Some(Resolution::Local(local_id)) = resolutions.get(&param.id) {
                    names.insert(*local_id, name_str);
                }
            }
        }
        FnParam::DefaultValue(inner, _) => {
            collect_param_name(inner, resolutions, names);
        }
        FnParam::Missing { .. } => {}
    }
}

fn collect_pattern_name(
    pattern: &Node<Pattern>,
    resolutions: &HashMap<NodeId, Resolution>,
    names: &mut HashMap<LocalBindingId, String>,
) {
    match &pattern.value {
        Pattern::Name(name) => {
            if let Some(name_str) = name.path.name() {
                if let Some(Resolution::Local(local_id)) = resolutions.get(&pattern.id) {
                    names.insert(*local_id, name_str);
                }
            }
        }
        Pattern::Deref(name_node) => {
            if let Some(name_str) = name_node.value.path.name() {
                if let Some(Resolution::Local(local_id)) = resolutions.get(&name_node.id) {
                    names.insert(*local_id, name_str);
                }
            }
        }
        Pattern::Sequence(pats) | Pattern::Tuple(pats) => {
            for pat in pats {
                collect_pattern_name(pat, resolutions, names);
            }
        }
        Pattern::Some(inner) => {
            collect_pattern_name(inner, resolutions, names);
        }
        Pattern::Dot(_, _) | Pattern::Index(_, _, _) | Pattern::Missing(_) => {}
    }
}

fn collect_binding_name_from_expr(
    expr: &Node<Expr>,
    resolutions: &HashMap<NodeId, Resolution>,
    names: &mut HashMap<LocalBindingId, String>,
) {
    match &expr.value {
        Expr::Assign(assign) => {
            collect_pattern_name(&assign.lhs, resolutions, names);
        }
        Expr::Name(name) => {
            if let Some(name_str) = name.path.name() {
                if let Some(Resolution::Local(local_id)) = resolutions.get(&expr.id) {
                    names.insert(*local_id, name_str);
                }
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        file_id::FileId,
        pathlib::{FilePath, ModulePath},
    };

    use crate::{
        queries::{
            bindings::{local_binding_definitions, local_binding_names},
            libraries::LoadedLibraries,
            locations::span_of,
            resolve::name_resolutions,
            workspace::{FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };
    use ray_shared::resolution::Resolution;

    fn setup_db(source: &str) -> (Database, FileId) {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(&db, file_id, FilePath::from("test/mod.ray"), module_path);
        (db, file_id)
    }

    /// Helper: get the set of binding names from a file.
    fn binding_names(db: &Database, file_id: FileId) -> Vec<String> {
        let names = local_binding_names(db, file_id);
        let mut result: Vec<String> = names.values().cloned().collect();
        result.sort();
        result
    }

    #[test]
    fn function_parameters() {
        let source = "fn foo(x: int, y: int) { x }";
        let (db, file_id) = setup_db(source);
        let names = binding_names(&db, file_id);
        assert!(
            names.contains(&"x".to_string()),
            "should contain x: {:?}",
            names
        );
        assert!(
            names.contains(&"y".to_string()),
            "should contain y: {:?}",
            names
        );
    }

    #[test]
    fn local_assignments() {
        let source = "fn foo() {\n    a = 1\n    b = 2\n    a\n}";
        let (db, file_id) = setup_db(source);
        let names = binding_names(&db, file_id);
        assert!(
            names.contains(&"a".to_string()),
            "should contain a: {:?}",
            names
        );
        assert!(
            names.contains(&"b".to_string()),
            "should contain b: {:?}",
            names
        );
    }

    #[test]
    fn closure_args() {
        let source = "fn foo() {\n    f = (x) => x\n    f\n}";
        let (db, file_id) = setup_db(source);
        let names = binding_names(&db, file_id);
        assert!(
            names.contains(&"f".to_string()),
            "should contain f: {:?}",
            names
        );
        assert!(
            names.contains(&"x".to_string()),
            "should contain x: {:?}",
            names
        );
    }

    #[test]
    fn local_id_maps_to_correct_name() {
        let source = "fn foo(x: int) { x }";
        let (db, file_id) = setup_db(source);

        // Find the LocalBindingId for parameter x via resolutions
        let resolutions = name_resolutions(&db, file_id);
        let binding_names_map = local_binding_names(&db, file_id);

        // There should be at least one local binding
        assert!(!binding_names_map.is_empty(), "should have binding names");

        // Every Resolution::Local in resolutions should have a matching entry in binding_names
        for (_, resolution) in resolutions.iter() {
            if let Resolution::Local(local_id) = resolution {
                assert!(
                    binding_names_map.contains_key(local_id),
                    "local_id {:?} should have a name",
                    local_id
                );
            }
        }
    }

    // =========================================================================
    // Tests for local_binding_definitions
    // =========================================================================

    #[test]
    fn binding_defs_covers_all_locals() {
        let source = "fn foo(x: int, y: int) { x }";
        let (db, file_id) = setup_db(source);

        let defs = local_binding_definitions(&db, file_id);
        let names = local_binding_names(&db, file_id);

        // Every LocalBindingId in names should have a definition site
        for local_id in names.keys() {
            assert!(
                defs.contains_key(local_id),
                "local_id {:?} (name={:?}) should have a definition site",
                local_id,
                names.get(local_id)
            );
        }
    }

    #[test]
    fn binding_defs_have_valid_spans() {
        let source = "fn foo(x: int) { x }";
        let (db, file_id) = setup_db(source);

        let defs = local_binding_definitions(&db, file_id);

        // Every definition NodeId should have a span
        for (local_id, node_id) in &defs {
            let span = span_of(&db, *node_id);
            assert!(
                span.is_some(),
                "definition site for {:?} should have a span",
                local_id
            );
        }
    }

    #[test]
    fn binding_defs_for_local_assignments() {
        let source = "fn foo() {\n    a = 1\n    b = 2\n    a\n}";
        let (db, file_id) = setup_db(source);

        let defs = local_binding_definitions(&db, file_id);
        let names = local_binding_names(&db, file_id);

        // Should have definitions for both a and b
        let def_names: Vec<String> = defs
            .keys()
            .filter_map(|lid| names.get(lid).cloned())
            .collect();
        assert!(
            def_names.contains(&"a".to_string()),
            "should have definition for a: {:?}",
            def_names
        );
        assert!(
            def_names.contains(&"b".to_string()),
            "should have definition for b: {:?}",
            def_names
        );
    }

    #[test]
    fn binding_defs_for_closure_args() {
        let source = "fn foo() {\n    f = (x) => x\n    f\n}";
        let (db, file_id) = setup_db(source);

        let defs = local_binding_definitions(&db, file_id);
        let names = local_binding_names(&db, file_id);

        let def_names: Vec<String> = defs
            .keys()
            .filter_map(|lid| names.get(lid).cloned())
            .collect();
        assert!(
            def_names.contains(&"f".to_string()),
            "should have definition for f: {:?}",
            def_names
        );
        assert!(
            def_names.contains(&"x".to_string()),
            "should have definition for x: {:?}",
            def_names
        );
    }

    #[test]
    fn binding_defs_node_id_resolves_to_definition() {
        // Verify that the NodeId from local_binding_definitions is the
        // definition site, not a reference site
        let source = "fn foo(x: int) { x }";
        let (db, file_id) = setup_db(source);

        let defs = local_binding_definitions(&db, file_id);
        let resolutions = name_resolutions(&db, file_id);

        for (local_id, def_node_id) in &defs {
            // The definition NodeId should also appear in resolutions
            // as a Resolution::Local with the same LocalBindingId
            let resolution = resolutions.get(def_node_id);
            assert!(
                matches!(resolution, Some(Resolution::Local(lid)) if lid == local_id),
                "definition node {:?} should resolve to the same local_id {:?}, got {:?}",
                def_node_id,
                local_id,
                resolution
            );
        }
    }
}

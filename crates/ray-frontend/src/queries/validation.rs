//! Validation queries for the incremental compiler.
//!
//! This module provides semantic validation that doesn't require full type inference.
//! These errors are caught early, before typechecking begins.

use std::collections::{HashMap, HashSet};

use ray_core::{
    ast::{
        Assign, Decl, Expr, Func, FuncSig, Node, PathBinding, Pattern, WalkItem, WalkScopeKind,
        walk_decl,
    },
    errors::{RayError, RayErrorKind},
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::pathlib::Path;
use ray_shared::{
    def::{DefId, DefKind},
    file_id::FileId,
    node_id::NodeId,
    pathlib::{FilePath, ItemPath},
    resolution::DefTarget,
    span::Source,
    ty::Ty,
};

use crate::{
    queries::{
        defs::{def_for_path, impl_def, trait_def},
        transform::file_ast,
        workspace::WorkspaceSnapshot,
    },
    query::{Database, Query},
};

/// Validate a definition and return any semantic errors.
///
/// This catches errors that don't require full type inference:
/// 1. Annotation policy violations (partial parameter annotations)
/// 2. Impl completeness (missing required trait methods)
/// 3. Extraneous impl methods (method not defined on trait)
///
/// These validations run before typechecking so users get early feedback.
#[query]
pub fn validate_def(db: &Database, def_id: DefId) -> Vec<RayError> {
    let file_result = file_ast(db, def_id.file);

    let Some(def_header) = file_result.defs.iter().find(|h| h.def_id == def_id) else {
        return vec![];
    };

    let Some(def_ast) = find_def_ast(&file_result.ast.decls, def_header.root_node) else {
        return vec![];
    };

    let filepath = file_result.ast.filepath.clone();
    let mut errors = Vec::new();

    match &def_header.kind {
        DefKind::Function { .. } | DefKind::Method => {
            validate_function(
                db,
                def_ast,
                def_id.file,
                &filepath,
                &file_result.source_map,
                &mut errors,
            );
        }
        DefKind::Impl => {
            validate_impl(
                db,
                def_ast,
                def_id,
                &filepath,
                &file_result.source_map,
                &mut errors,
            );
        }
        DefKind::Trait => {
            validate_trait(
                db,
                def_ast,
                def_id.file,
                &filepath,
                &file_result.source_map,
                &mut errors,
            );
        }
        // Other definition kinds don't have special validation
        _ => {}
    }

    errors
}

/// Validate a function declaration for annotation policy violations and qualifier existence.
fn validate_function(
    db: &Database,
    decl: &Node<Decl>,
    file_id: FileId,
    filepath: &FilePath,
    srcmap: &SourceMap,
    errors: &mut Vec<RayError>,
) {
    let (sig, body) = match &decl.value {
        Decl::Func(func) => (&func.sig, &func.body),
        Decl::FnSig(sig) => (sig, &None),
        _ => return,
    };

    validate_annotation_policy(sig, body, filepath, srcmap, errors);
    validate_qualifiers(db, sig, file_id, filepath, srcmap, errors);

    // Only validate mutability for declarations with bodies (not FnSig)
    if body.is_some() {
        validate_mutability(decl, filepath, srcmap, errors);
    }
}

/// Validate the annotation policy for a function signature.
///
/// The rule is: either ALL non-self parameters must have annotations,
/// or NONE of them do. Partial annotation is an error.
fn validate_annotation_policy(
    sig: &FuncSig,
    body: &Option<Box<Node<Expr>>>,
    filepath: &FilePath,
    srcmap: &SourceMap,
    errors: &mut Vec<RayError>,
) {
    // Skip if no parameters
    if sig.params.is_empty() {
        return;
    }

    // Count annotated and unannotated parameters (excluding self)
    let mut annotated_count = 0;
    let mut unannotated_params = Vec::new();

    for (idx, param) in sig.params.iter().enumerate() {
        let is_self = idx == 0 && param.value.name().is_self();
        if is_self {
            continue;
        }

        if param.value.ty().is_some() {
            annotated_count += 1;
        } else {
            unannotated_params.push(param);
        }
    }

    // If all params are annotated or all are unannotated, no partial annotation error
    let non_self_param_count = sig.params.len()
        - sig
            .params
            .first()
            .map(|p| if p.value.name().is_self() { 1 } else { 0 })
            .unwrap_or(0);

    let is_partial_annotation = annotated_count > 0 && annotated_count < non_self_param_count;

    if is_partial_annotation {
        // Partial annotation is an error
        for param in unannotated_params {
            errors.push(RayError {
                msg: format!(
                    "parameter `{}` must have a type annotation (partial annotation not allowed)",
                    param.value
                ),
                src: vec![Source {
                    span: Some(srcmap.span_of(param)),
                    filepath: filepath.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Type,
                context: Some("annotation policy validation".to_string()),
            });
        }
    }

    // Check return type for methods with block bodies when params are annotated
    // If params are annotated but return type is missing with a block body, that's an error
    let all_annotated = annotated_count == non_self_param_count && non_self_param_count > 0;
    if all_annotated && sig.ret_ty.is_none() && !method_allows_inferred_return(body) {
        errors.push(RayError {
            msg: "method must have a return type annotation unless using `=>`".to_string(),
            src: vec![Source {
                span: Some(sig.span),
                filepath: filepath.clone(),
                ..Default::default()
            }],
            kind: RayErrorKind::Type,
            context: Some("annotation policy validation".to_string()),
        });
    }
}

/// Check if a method body allows inferred return type (arrow body).
fn method_allows_inferred_return(body: &Option<Box<Node<Expr>>>) -> bool {
    match body {
        Some(b) => !matches!(b.value, Expr::Block(_)),
        None => true, // No body = signature only (trait method)
    }
}

/// Validate that all qualifiers (where clauses) reference existing traits.
///
/// Each qualifier must be a trait type (Ty::Proj or Ty::Const with a valid path).
/// If the trait doesn't exist, an error is reported.
fn validate_qualifiers(
    db: &Database,
    sig: &FuncSig,
    file_id: FileId,
    filepath: &FilePath,
    _srcmap: &SourceMap,
    errors: &mut Vec<RayError>,
) {
    // Get the module path for this file to resolve unqualified names
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let module_path = match workspace.files.get(&file_id) {
        Some(info) => info.module_path.clone(),
        None => return,
    };

    for qual in &sig.qualifiers {
        let qual_ty = qual.clone_value();
        let qual_span = qual.span();

        // Extract the path from the qualifier type
        let path = match &qual_ty {
            Ty::Proj(path, _) => path.clone(),
            Ty::Const(path) => path.clone(),
            _ => {
                // Not a valid trait reference - this would be caught elsewhere
                continue;
            }
        };

        // Build ItemPath - if unqualified (single name), use current module
        let mut item_path = ItemPath::from(path.clone());
        if item_path.module.is_empty() {
            // Unqualified name - look up in current module
            item_path.module = module_path.clone();
        }

        // Try to find the definition
        let target = def_for_path(db, item_path);

        match target {
            Some(t) => {
                // Check that it's actually a trait
                if trait_def(db, t).is_none() {
                    errors.push(RayError {
                        msg: format!("`{}` is not a trait", path),
                        src: vec![Source {
                            span: qual_span.copied(),
                            filepath: filepath.clone(),
                            ..Default::default()
                        }],
                        kind: RayErrorKind::Type,
                        context: Some("qualifier validation".to_string()),
                    });
                }
            }
            None => {
                errors.push(RayError {
                    msg: format!("trait `{}` is not defined", path),
                    src: vec![Source {
                        span: qual_span.copied(),
                        filepath: filepath.clone(),
                        ..Default::default()
                    }],
                    kind: RayErrorKind::Type,
                    context: Some("qualifier validation".to_string()),
                });
            }
        }
    }
}

// ============================================================================
// Mutability checking using AST walker
// ============================================================================

/// Information about a binding's mutability.
#[derive(Clone, Debug)]
struct BindingInfo {
    is_mut: bool,
}

/// Context for tracking variable mutability during expression traversal.
struct MutabilityCtx {
    /// Stack of scope bindings - each scope has its own map.
    scope_stack: Vec<HashMap<Path, BindingInfo>>,
}

impl MutabilityCtx {
    /// Create a new empty context.
    fn new() -> Self {
        Self {
            scope_stack: vec![HashMap::new()],
        }
    }

    /// Push a new scope onto the stack.
    fn push_scope(&mut self) {
        self.scope_stack.push(HashMap::new());
    }

    /// Pop the current scope from the stack.
    fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }

    /// Register a binding from a pattern in the current scope.
    fn register_pattern(&mut self, pattern: &Node<Pattern>, is_mut: bool) {
        if let Some(current_scope) = self.scope_stack.last_mut() {
            for node in pattern.paths() {
                let PathBinding { path, .. } = node.value;
                current_scope.insert(path.clone(), BindingInfo { is_mut });
            }
        }
    }

    /// Register a single name binding in the current scope.
    fn register_name(&mut self, name: &Path, is_mut: bool) {
        if let Some(current_scope) = self.scope_stack.last_mut() {
            current_scope.insert(name.clone(), BindingInfo { is_mut });
        }
    }

    /// Check if a path refers to a mutable binding (searches all scopes).
    fn is_mutable(&self, path: &Path) -> Option<bool> {
        // Search from innermost to outermost scope
        for scope in self.scope_stack.iter().rev() {
            if let Some(info) = scope.get(path) {
                return Some(info.is_mut);
            }
        }
        None
    }
}

/// Validate mutability for all assignments in a declaration using the AST walker.
fn validate_mutability(
    decl: &Node<Decl>,
    filepath: &FilePath,
    srcmap: &SourceMap,
    errors: &mut Vec<RayError>,
) {
    let mut ctx = MutabilityCtx::new();

    // Use the AST walker to traverse the declaration.
    // The walker emits WalkItem::Decl first, which we use to register parameters.
    for item in walk_decl(decl) {
        match item {
            WalkItem::EnterScope(kind) => match kind {
                WalkScopeKind::Block
                | WalkScopeKind::Closure
                | WalkScopeKind::Function
                | WalkScopeKind::FileMain => {
                    ctx.push_scope();
                }
                WalkScopeKind::Module | WalkScopeKind::Impl | WalkScopeKind::Trait => {}
            },
            WalkItem::ExitScope(kind) => match kind {
                WalkScopeKind::Block
                | WalkScopeKind::Closure
                | WalkScopeKind::Function
                | WalkScopeKind::FileMain => {
                    ctx.pop_scope();
                }
                WalkScopeKind::Module | WalkScopeKind::Impl | WalkScopeKind::Trait => {}
            },
            WalkItem::Decl(decl_node) => {
                // Register parameters for the outer function declaration
                if let Decl::Func(func) = &decl_node.value {
                    for param in &func.sig.params {
                        ctx.register_name(&param.value.name(), false);
                    }
                }
            }
            WalkItem::Func(func) => {
                // Impl methods - register parameters after EnterScope(Function)
                for param in &func.value.sig.params {
                    ctx.register_name(&param.value.name(), false);
                }
            }
            WalkItem::Expr(expr) => match &expr.value {
                Expr::Assign(assign) => {
                    validate_assignment(assign, &mut ctx, filepath, srcmap, errors);
                }
                Expr::For(for_expr) => {
                    // For loops introduce a binding for the loop variable
                    ctx.register_pattern(&for_expr.pat, false);
                }
                Expr::Func(func) => {
                    // Nested function expression - register parameters
                    for param in &func.sig.params {
                        ctx.register_name(&param.value.name(), false);
                    }
                }
                Expr::Closure(closure) => {
                    // Closure expression - register arguments as immutable
                    for arg in &closure.args.items {
                        if let Expr::Name(name) = &arg.value {
                            ctx.register_name(&name.path, false);
                        }
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }
}

/// Validate a single assignment for mutability.
fn validate_assignment(
    assign: &Assign,
    ctx: &mut MutabilityCtx,
    filepath: &FilePath,
    srcmap: &SourceMap,
    errors: &mut Vec<RayError>,
) {
    // Check each path in the LHS pattern
    for node in assign.lhs.paths() {
        let PathBinding { path, is_lvalue } = node.value;

        // is_lvalue means it's a dereference like *ptr, not a simple name
        // When is_lvalue is true, we're not checking mutability of the name itself
        if is_lvalue {
            continue;
        }

        match ctx.is_mutable(path) {
            Some(is_mut) => {
                // Known binding - check mutability
                if !is_mut {
                    // Assigning to an immutable binding is an error
                    errors.push(RayError {
                        msg: format!("cannot assign to immutable identifier `{}`", path),
                        src: vec![Source {
                            span: Some(srcmap.span_of(&assign.lhs)),
                            filepath: filepath.clone(),
                            ..Default::default()
                        }],
                        kind: RayErrorKind::Type,
                        context: Some("mutability validation".to_string()),
                    });
                }
                // Mutable binding - OK
            }
            None => {
                // New binding - register it in current scope
                ctx.register_pattern(&assign.lhs, assign.is_mut);
            }
        }
    }
}

/// Validate an impl block for completeness.
fn validate_impl(
    db: &Database,
    decl: &Node<Decl>,
    def_id: DefId,
    filepath: &FilePath,
    srcmap: &SourceMap,
    errors: &mut Vec<RayError>,
) {
    let Decl::Impl(im) = &decl.value else { return };

    // Validate individual methods in the impl (annotation policy)
    // This runs for both trait impls and inherent impls
    if let Some(funcs) = &im.funcs {
        for func in funcs {
            validate_impl_method(func, filepath, srcmap, errors);
        }
    }

    // Validate mutability for the entire impl block
    // The walker emits WalkItem::Func for each method, so this covers all methods
    validate_mutability(decl, filepath, srcmap, errors);

    let Some(impl_definition) = impl_def(db, DefTarget::Workspace(def_id)) else {
        return;
    };

    // Inherent impl - completeness check not needed
    let Some(ref trait_ty) = impl_definition.trait_ty else {
        return;
    };

    // Get the trait path from the trait type
    let trait_path = match trait_ty {
        Ty::Const(p) | Ty::Proj(p, _) => p.clone(),
        _ => return,
    };

    // Look up the trait definition
    let Some(trait_target) = def_for_path(db, trait_path) else {
        return;
    };

    // Trait not found - this error would be caught by name resolution
    let Some(trait_definition) = trait_def(db, trait_target) else {
        return;
    };

    // Validate type argument arity (only for trait impls, not object impls)
    if !im.is_object {
        let ty_args_count = match im.ty.clone_value() {
            Ty::Proj(_, args) => args.len(),
            _ => 0,
        };
        let expected_count = trait_definition.type_params.len();

        if ty_args_count != expected_count {
            errors.push(RayError {
                msg: format!(
                    "trait `{}` expected {} type argument(s) but found {}",
                    trait_definition.path.item_name().unwrap_or("?"),
                    expected_count,
                    ty_args_count
                ),
                src: vec![Source {
                    span: im.ty.span().copied(),
                    filepath: filepath.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Type,
                context: Some("type argument arity validation".to_string()),
            });
        }
    }

    // Check that all required methods are implemented (compare by name only)
    let implemented_method_names: HashSet<_> =
        impl_definition.methods.iter().map(|m| &m.name).collect();

    for required_method in &trait_definition.methods {
        if !implemented_method_names.contains(&required_method.name) {
            errors.push(RayError {
                msg: format!(
                    "impl `{}` is missing required method `{}`",
                    trait_definition.path.item_name().unwrap_or("?"),
                    required_method.name
                ),
                src: vec![Source {
                    span: Some(srcmap.span_of(decl)),
                    filepath: filepath.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Type,
                context: Some("impl completeness validation".to_string()),
            });
        }
    }

    // Check for extraneous methods (methods not defined on trait)
    let trait_method_names: HashSet<_> = trait_definition.methods.iter().map(|m| &m.name).collect();

    for impl_method in &impl_definition.methods {
        if !trait_method_names.contains(&impl_method.name) {
            errors.push(RayError {
                msg: format!(
                    "method `{}` does not exist on trait `{}`",
                    impl_method.name,
                    trait_definition.path.item_name().unwrap_or("?")
                ),
                src: vec![Source {
                    span: Some(srcmap.span_of(decl)),
                    filepath: filepath.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Type,
                context: Some("impl completeness validation".to_string()),
            });
        }
    }
}

/// Validate an impl method for annotation policy.
fn validate_impl_method(
    decl: &Node<Decl>,
    filepath: &FilePath,
    srcmap: &SourceMap,
    errors: &mut Vec<RayError>,
) {
    let Decl::Func(func) = &decl.value else {
        unreachable!("impl funcs should only contain Decl::Func");
    };
    validate_annotation_policy(&func.sig, &func.body, filepath, srcmap, errors);
}

/// Validate a trait definition.
fn validate_trait(
    db: &Database,
    decl: &Node<Decl>,
    file_id: FileId,
    filepath: &FilePath,
    srcmap: &SourceMap,
    errors: &mut Vec<RayError>,
) {
    let Decl::Trait(tr) = &decl.value else { return };

    // Validate each method signature in the trait
    for field in &tr.fields {
        match &field.value {
            Decl::FnSig(sig) => {
                validate_trait_method_signature(db, sig, file_id, filepath, srcmap, errors);
            }
            Decl::Func(func) => {
                // Default method implementation
                validate_annotation_policy(&func.sig, &func.body, filepath, srcmap, errors);
                validate_qualifiers(db, &func.sig, file_id, filepath, srcmap, errors);
            }
            _ => {}
        }
    }
}

/// Validate a trait method signature for annotation policy and qualifier existence.
fn validate_trait_method_signature(
    db: &Database,
    sig: &FuncSig,
    file_id: FileId,
    filepath: &FilePath,
    srcmap: &SourceMap,
    errors: &mut Vec<RayError>,
) {
    // In traits, methods should be fully annotated (except self)
    // Note: The first parameter named `self` can be unannotated and will be filled in
    for (idx, param) in sig.params.iter().enumerate() {
        let is_self = idx == 0 && param.value.name().is_self();
        if is_self {
            continue;
        }

        if param.value.ty().is_none() {
            errors.push(RayError {
                msg: format!("parameter `{}` must have a type annotation", param.value),
                src: vec![Source {
                    span: Some(srcmap.span_of(param)),
                    filepath: filepath.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Type,
                context: Some("trait method annotation validation".to_string()),
            });
        }
    }

    // Return type is required for trait methods unless they're arrow bodies
    // (which isn't typical for trait method signatures)
    if sig.ret_ty.is_none() && !sig.has_body {
        // For signatures without bodies (pure declarations), check if any params are annotated
        // If params are annotated, return type should also be annotated
        let has_annotated_params = sig.params.iter().enumerate().any(|(idx, p)| {
            let is_self = idx == 0 && p.value.name().is_self();
            !is_self && p.value.ty().is_some()
        });

        if has_annotated_params {
            errors.push(RayError {
                msg: "trait method must have a return type annotation".to_string(),
                src: vec![Source {
                    span: Some(sig.span),
                    filepath: filepath.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Type,
                context: Some("trait method annotation validation".to_string()),
            });
        }
    }

    // Validate qualifiers (where clauses)
    validate_qualifiers(db, sig, file_id, filepath, srcmap, errors);
}

/// Find a declaration AST node by its root NodeId.
fn find_def_ast(decls: &[Node<Decl>], root_node: NodeId) -> Option<&Node<Decl>> {
    for decl in decls {
        if decl.id == root_node {
            return Some(decl);
        }

        // Check nested declarations (e.g., methods in impl blocks, trait methods)
        if let Some(nested) = find_nested_def(decl, root_node) {
            return Some(nested);
        }
    }
    None
}

/// Find a nested declaration within a parent declaration.
fn find_nested_def(parent: &Node<Decl>, root_node: NodeId) -> Option<&Node<Decl>> {
    match &parent.value {
        Decl::Trait(tr) => {
            for field in &tr.fields {
                if field.id == root_node {
                    return Some(field);
                }
            }
        }
        Decl::Impl(im) => {
            // Check extern declarations
            if let Some(externs) = &im.externs {
                for ext in externs {
                    if ext.id == root_node {
                        return Some(ext);
                    }
                }
            }
        }
        _ => {}
    }
    None
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::pathlib::{FilePath, ModulePath};

    use crate::{
        queries::{
            defs::impls_in_module,
            libraries::LoadedLibraries,
            parse::parse_file,
            validation::validate_def,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    #[test]
    fn validate_def_no_errors_for_fully_annotated_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Fully annotated function
        FileSource::new(
            &db,
            file_id,
            r#"fn add(x: int, y: int) -> int { x + y }"#.to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let add_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "add")
            .expect("should find add function");

        let errors = validate_def(&db, add_def.def_id);
        assert!(errors.is_empty(), "Expected no errors, got: {:?}", errors);
    }

    #[test]
    fn validate_def_no_errors_for_unannotated_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Completely unannotated function (OK - will be inferred)
        FileSource::new(&db, file_id, r#"fn foo(x, y) { x + y }"#.to_string());

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo function");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for fully unannotated function"
        );
    }

    #[test]
    fn validate_def_error_for_partial_annotation() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Partially annotated function (ERROR)
        FileSource::new(&db, file_id, r#"fn bad(x: int, y) { x + y }"#.to_string());

        let parse_result = parse_file(&db, file_id);
        let bad_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "bad")
            .expect("should find bad function");

        let errors = validate_def(&db, bad_def.def_id);
        assert!(!errors.is_empty(), "Expected error for partial annotation");
        assert!(
            errors[0].msg.contains("must have a type annotation"),
            "Error message should mention type annotation: {}",
            errors[0].msg
        );
    }

    #[test]
    fn validate_def_no_errors_for_return_elided_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Arrow body function - return type elided is OK
        FileSource::new(&db, file_id, r#"fn double(x: int) => x * 2"#.to_string());

        let parse_result = parse_file(&db, file_id);
        let double_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "double")
            .expect("should find double function");

        let errors = validate_def(&db, double_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for arrow body function"
        );
    }

    #[test]
    fn validate_def_error_for_missing_return_with_block_body() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Block body with annotated params but no return type
        FileSource::new(&db, file_id, r#"fn bad(x: int) { x * 2 }"#.to_string());

        let parse_result = parse_file(&db, file_id);
        let bad_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "bad")
            .expect("should find bad function");

        let errors = validate_def(&db, bad_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for missing return type with block body"
        );
        assert!(
            errors[0].msg.contains("return type annotation"),
            "Error message should mention return type: {}",
            errors[0].msg
        );
    }

    #[test]
    fn validate_def_impl_completeness_error() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Trait with method, impl missing the method
        let source = r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

struct Point { x: int, y: int }

impl ToStr[Point] {
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Find the impl using impls_in_module
        let impls = impls_in_module(&db, module_path);
        assert_eq!(impls.len(), 1, "Should find 1 impl");
        let impl_def_id = impls[0];

        let errors = validate_def(&db, impl_def_id);
        assert!(!errors.is_empty(), "Expected error for missing method");
        assert!(
            errors[0].msg.contains("missing required method"),
            "Error message should mention missing method: {}",
            errors[0].msg
        );
    }

    #[test]
    fn validate_def_impl_extraneous_method_error() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Trait with one method, impl has extra method
        let source = r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

struct Point { x: int, y: int }

impl ToStr[Point] {
    fn to_str(self: Point) -> string => "Point"
    fn extra(self: Point) -> int => 42
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Find the impl using impls_in_module
        let impls = impls_in_module(&db, module_path);
        assert_eq!(impls.len(), 1, "Should find 1 impl");
        let impl_def_id = impls[0];

        let errors = validate_def(&db, impl_def_id);
        assert!(!errors.is_empty(), "Expected error for extraneous method");
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("does not exist on trait")),
            "Error message should mention extraneous method: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_no_errors_for_complete_impl() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Complete impl with all required methods
        let source = r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

struct Point { x: int, y: int }

impl ToStr[Point] {
    fn to_str(self: Point) -> string => "Point"
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Find the impl using impls_in_module
        let impls = impls_in_module(&db, module_path);
        assert_eq!(impls.len(), 1, "Should find 1 impl");
        let impl_def_id = impls[0];

        let errors = validate_def(&db, impl_def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for complete impl, got: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_no_errors_for_inherent_impl() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Inherent impl (no trait)
        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn new(x: int, y: int): Point => Point { x, y }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Find the impl using impls_in_module
        let impls = impls_in_module(&db, module_path);
        assert_eq!(impls.len(), 1, "Should find 1 impl");
        let impl_def_id = impls[0];

        let errors = validate_def(&db, impl_def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for inherent impl, got: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_error_for_undefined_trait_in_qualifier() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with qualifier referencing undefined trait
        let source = r#"fn foo['a](x: 'a) -> 'a where UndefinedTrait['a] { x }"#;
        FileSource::new(&db, file_id, source.to_string());

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo function");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(!errors.is_empty(), "Expected error for undefined trait");
        assert!(
            errors[0].msg.contains("is not defined"),
            "Error message should mention trait not defined: {}",
            errors[0].msg
        );
    }

    #[test]
    fn validate_def_no_error_for_defined_trait_in_qualifier() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Trait is defined, qualifier references it
        let source = r#"
trait Show['a] {
    fn show(self: 'a) -> string
}

fn display['a](x: 'a) -> string where Show['a] { x.show() }
"#;
        FileSource::new(&db, file_id, source.to_string());

        let parse_result = parse_file(&db, file_id);
        let display_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "display")
            .expect("should find display function");

        let errors = validate_def(&db, display_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for valid qualifier, got: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_error_for_struct_used_as_trait_in_qualifier() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Point is a struct, not a trait
        let source = r#"
struct Point { x: int, y: int }

fn foo['a](x: 'a) -> 'a where Point['a] { x }
"#;
        FileSource::new(&db, file_id, source.to_string());

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo function");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for struct used as trait"
        );
        assert!(
            errors[0].msg.contains("is not a trait"),
            "Error message should mention it's not a trait: {}",
            errors[0].msg
        );
    }

    #[test]
    fn validate_def_error_for_wrong_type_arg_arity_in_impl() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Trait takes 1 type param, but impl provides 2
        let source = r#"
trait Show['a] {
    fn show(self: 'a) -> string
}

struct Point { x: int, y: int }

impl Show[Point, int] {
    fn show(self: Point) -> string => "Point"
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Find the impl using impls_in_module
        let impls = impls_in_module(&db, module_path);
        assert_eq!(impls.len(), 1, "Should find 1 impl");
        let impl_def_id = impls[0];

        let errors = validate_def(&db, impl_def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for wrong type argument arity"
        );
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("expected") && e.msg.contains("type argument")),
            "Error message should mention type argument arity: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_no_error_for_correct_type_arg_arity_in_impl() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Trait takes 1 type param, impl provides 1 - correct
        let source = r#"
trait Show['a] {
    fn show(self: 'a) -> string
}

struct Point { x: int, y: int }

impl Show[Point] {
    fn show(self: Point) -> string => "Point"
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Find the impl using impls_in_module
        let impls = impls_in_module(&db, module_path);
        assert_eq!(impls.len(), 1, "Should find 1 impl");
        let impl_def_id = impls[0];

        let errors = validate_def(&db, impl_def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for correct type argument arity, got: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_error_for_assign_to_immutable() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function that tries to assign to immutable parameter
        let source = r#"fn foo(x: int) -> int { x = 5; x }"#;
        FileSource::new(&db, file_id, source.to_string());

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo function");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for assignment to immutable parameter"
        );
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("cannot assign to immutable")),
            "Error message should mention cannot assign to immutable: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_no_error_for_assign_to_mutable() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function that declares mutable and assigns
        let source = r#"fn foo(x: int) -> int { mut y = x; y = 5; y }"#;
        FileSource::new(&db, file_id, source.to_string());

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo function");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for assignment to mutable variable, got: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_error_for_reassign_to_immutable_local() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function that declares immutable local and tries to reassign
        // In Ray, `x = 5` creates an immutable binding, `x = 10` tries to reassign
        let source = r#"fn foo() -> int { x = 5; x = 10; x }"#;
        FileSource::new(&db, file_id, source.to_string());

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo function");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for reassignment to immutable local"
        );
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("cannot assign to immutable")),
            "Error message should mention cannot assign to immutable: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_closure_has_own_scope() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Outer function has param x, closure also has param x
        // The closure x should shadow the outer x in its scope
        // Closure syntax: (args) => body
        let source = r#"fn outer(x: int) -> int {
            inner = (x: int) => x
            inner(x)
        }"#;
        FileSource::new(&db, file_id, source.to_string());

        let parse_result = parse_file(&db, file_id);
        let outer_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "outer")
            .expect("should find outer function");

        let errors = validate_def(&db, outer_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for closure with shadowed param, got: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_error_for_assign_to_immutable_in_closure() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Closure tries to assign to its immutable parameter
        // Closure syntax: (args) => body
        let source = r#"fn outer() -> int {
            inner = (y: int) => { y = 10; y }
            inner(5)
        }"#;
        FileSource::new(&db, file_id, source.to_string());

        let parse_result = parse_file(&db, file_id);
        let outer_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "outer")
            .expect("should find outer function");

        let errors = validate_def(&db, outer_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for assignment to immutable param in closure"
        );
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("cannot assign to immutable")),
            "Error should mention immutable assignment: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_nested_function_has_own_scope() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Outer function has param x, nested function also has param x
        // The nested function's x should shadow the outer x in its scope
        let source = r#"fn outer(x: int) -> int {
            fn inner(x: int) -> int { x }
            inner(x)
        }"#;
        FileSource::new(&db, file_id, source.to_string());

        let parse_result = parse_file(&db, file_id);
        let outer_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "outer")
            .expect("should find outer function");

        let errors = validate_def(&db, outer_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for nested function with shadowed param, got: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_error_for_assign_to_immutable_in_nested_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Nested function tries to assign to its immutable parameter
        let source = r#"fn outer() -> int {
            fn inner(y: int) -> int { y = 10; y }
            inner(5)
        }"#;
        FileSource::new(&db, file_id, source.to_string());

        let parse_result = parse_file(&db, file_id);
        let outer_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "outer")
            .expect("should find outer function");

        let errors = validate_def(&db, outer_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for assignment to immutable param in nested function"
        );
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("cannot assign to immutable")),
            "Error should mention immutable assignment: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_error_for_assign_to_immutable_in_impl_method() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Impl method tries to assign to its immutable parameter
        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn bad(self: Point) -> int { self = Point { x: 0, y: 0 }; 0 }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Find the impl using impls_in_module
        let impls = impls_in_module(&db, module_path);
        assert_eq!(impls.len(), 1, "Should find 1 impl");
        let impl_def_id = impls[0];

        let errors = validate_def(&db, impl_def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for assignment to immutable param in impl method"
        );
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("cannot assign to immutable")),
            "Error should mention immutable assignment: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_no_error_for_mutable_in_impl_method() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Impl method correctly uses mutable local
        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn good(self: Point) -> int { mut x = 0; x = 5; x }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Find the impl using impls_in_module
        let impls = impls_in_module(&db, module_path);
        assert_eq!(impls.len(), 1, "Should find 1 impl");
        let impl_def_id = impls[0];

        let errors = validate_def(&db, impl_def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for mutable variable in impl method, got: {:?}",
            errors
        );
    }
}

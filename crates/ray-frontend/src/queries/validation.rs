//! Validation queries for the incremental compiler.
//!
//! This module provides semantic validation that doesn't require full type inference.
//! These errors are caught early, before typechecking begins.

use std::{
    collections::{HashMap, HashSet},
    ops::Deref,
    sync::Arc,
};

use ray_core::{
    ast::{
        Assign, Decl, Expr, FuncSig, Node, PathBinding, Pattern, WalkItem, WalkScopeKind, walk_decl,
    },
    errors::{RayError, RayErrorKind},
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::{
    def::{DefId, DefKind},
    file_id::FileId,
    graph::DirectedGraph,
    node_id::NodeId,
    pathlib::{FilePath, ItemPath, Path},
    resolution::{DefTarget, Resolution},
    span::{Source, Span},
    ty::Ty,
};

use crate::{
    queries::{
        defs::{def_for_path, find_def_ast, impl_def, struct_def, trait_def},
        resolve::name_resolutions,
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

    // Universal: validate all type annotations for invalid ref nesting (e.g., `id *mut T`)
    validate_type_annotations(def_ast, &filepath, &mut errors);

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
        DefKind::Struct => {
            validate_struct_fields(def_ast, &filepath, &mut errors);
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

    validate_annotation_policy(sig, filepath, srcmap, errors);
    validate_qualifiers(db, sig, file_id, filepath, errors);

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
    errors: &mut Vec<RayError>,
) {
    let resolutions = name_resolutions(db, file_id);

    for qual in &sig.qualifiers {
        let qual_span = qual.span();

        // Extract the path for error messages
        let path = match qual.value() {
            Ty::Proj(path, _) | Ty::Const(path) => path.clone(),
            _ => continue,
        };

        // Use name resolutions to find the actual definition target.
        // The first synthetic ID corresponds to the qualifier's base path.
        let target = qual
            .synthetic_ids()
            .first()
            .and_then(|id| match resolutions.get(id) {
                Some(Resolution::Def(target)) => Some(target.clone()),
                _ => None,
            });

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

    /// Register new bindings from an assignment pattern.
    /// Only registers bindable paths that are not already in scope.
    fn register_new_bindings(&mut self, pattern: &Node<Pattern>, is_mut: bool) {
        for node in pattern.paths() {
            let PathBinding { path, is_bindable } = node.value;
            if is_bindable && self.is_mutable(path).is_none() {
                self.register_name(path, is_mut);
            }
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
                    validate_assignment(assign, &ctx, filepath, srcmap, errors);
                    ctx.register_new_bindings(&assign.lhs, assign.is_mut);
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
/// New bindings must be registered before calling this function.
fn validate_assignment(
    assign: &Assign,
    ctx: &MutabilityCtx,
    filepath: &FilePath,
    srcmap: &SourceMap,
    errors: &mut Vec<RayError>,
) {
    for node in assign.lhs.paths() {
        let PathBinding { path, is_bindable } = node.value;
        if !is_bindable {
            continue;
        }

        if let Some(false) = ctx.is_mutable(path) {
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
    }
}

// ============================================================================
// Type annotation validation — universal ref nesting check
// ============================================================================

/// Check a single type for invalid reference nesting (e.g., `id` wrapping `*mut`).
fn check_ref_nesting(
    ty: &Ty,
    span: Option<&Span>,
    filepath: &FilePath,
    errors: &mut Vec<RayError>,
) {
    if ty.contains_invalid_ref_nesting() {
        errors.push(RayError {
            msg: format!(
                "`id` references cannot wrap `*mut` references in type `{}`",
                ty
            ),
            src: vec![Source {
                span: span.copied(),
                filepath: filepath.clone(),
                ..Default::default()
            }],
            kind: RayErrorKind::Type,
            context: Some("type annotation validation".to_string()),
        });
    }
}

/// Check all type annotations in a function signature for invalid reference nesting.
fn check_sig_ref_nesting(sig: &FuncSig, filepath: &FilePath, errors: &mut Vec<RayError>) {
    for param in &sig.params {
        if let Some(parsed_ty) = param.value.parsed_ty() {
            check_ref_nesting(&parsed_ty.value().ty, parsed_ty.span(), filepath, errors);
        }
    }
    if let Some(ret_ty) = &sig.ret_ty {
        check_ref_nesting(ret_ty.value(), ret_ty.span(), filepath, errors);
    }
    for qual in &sig.qualifiers {
        check_ref_nesting(qual.value(), qual.span(), filepath, errors);
    }
}

/// Validate all type annotations in a declaration for invalid reference nesting.
///
/// Walks the entire declaration AST and checks every user-written type annotation
/// for patterns like `id *mut T`, which is never valid.
fn validate_type_annotations(decl: &Node<Decl>, filepath: &FilePath, errors: &mut Vec<RayError>) {
    for item in walk_decl(decl) {
        match item {
            WalkItem::Decl(decl_node) => match &decl_node.value {
                Decl::Func(func) => {
                    check_sig_ref_nesting(&func.sig, filepath, errors);
                }
                Decl::FnSig(sig) => {
                    check_sig_ref_nesting(sig, filepath, errors);
                }
                Decl::TypeAlias(_, parsed_ty) => {
                    check_ref_nesting(parsed_ty.value(), parsed_ty.span(), filepath, errors);
                }
                Decl::Struct(st) => {
                    if let Some(fields) = &st.fields {
                        for field in fields {
                            if let Some(parsed_ty) = &field.value.ty {
                                check_ref_nesting(
                                    &parsed_ty.value().ty,
                                    parsed_ty.span(),
                                    filepath,
                                    errors,
                                );
                            }
                        }
                    }
                }
                Decl::Trait(tr) => {
                    check_ref_nesting(tr.ty.value(), tr.ty.span(), filepath, errors);
                    if let Some(super_trait) = &tr.super_trait {
                        check_ref_nesting(
                            super_trait.value(),
                            super_trait.span(),
                            filepath,
                            errors,
                        );
                    }
                }
                Decl::Impl(imp) => {
                    check_ref_nesting(imp.ty.value(), imp.ty.span(), filepath, errors);
                    for qual in &imp.qualifiers {
                        check_ref_nesting(qual.value(), qual.span(), filepath, errors);
                    }
                }
                Decl::Name(name, _) | Decl::Mutable(name, _) => {
                    if let Some(parsed_ty) = &name.value.ty {
                        check_ref_nesting(
                            &parsed_ty.value().ty,
                            parsed_ty.span(),
                            filepath,
                            errors,
                        );
                    }
                }
                _ => {}
            },
            WalkItem::Expr(expr) => match &expr.value {
                Expr::Cast(cast) => {
                    check_ref_nesting(cast.ty.value(), cast.ty.span(), filepath, errors);
                }
                Expr::New(new_expr) => {
                    check_ref_nesting(
                        new_expr.ty.value.value(),
                        new_expr.ty.value.span(),
                        filepath,
                        errors,
                    );
                }
                Expr::TypeAnnotated(_, parsed) => {
                    check_ref_nesting(
                        &parsed.value.value().ty,
                        parsed.value.span(),
                        filepath,
                        errors,
                    );
                }
                Expr::Type(parsed) => {
                    check_ref_nesting(&parsed.value().ty, parsed.span(), filepath, errors);
                }
                Expr::Name(name) => {
                    if let Some(parsed_ty) = &name.ty {
                        check_ref_nesting(
                            &parsed_ty.value().ty,
                            parsed_ty.span(),
                            filepath,
                            errors,
                        );
                    }
                }
                _ => {}
            },
            WalkItem::Name(name) => {
                if let Some(parsed_ty) = &name.value.ty {
                    check_ref_nesting(&parsed_ty.value().ty, parsed_ty.span(), filepath, errors);
                }
            }
            _ => {}
        }
    }
}

/// Validate struct field types for reference restrictions.
///
/// Rejects `*mut T` anywhere in a field type (unique references are not allowed in struct fields).
/// Invalid reference nesting like `id *mut T` is caught by `validate_type_annotations`.
fn validate_struct_fields(decl: &Node<Decl>, filepath: &FilePath, errors: &mut Vec<RayError>) {
    let Decl::Struct(st) = &decl.value else {
        return;
    };

    let Some(fields) = &st.fields else { return };

    for field in fields {
        let Some(parsed_ty) = &field.value.ty else {
            continue;
        };

        let ty = &parsed_ty.value().ty;

        if ty.contains_mut_ref() {
            errors.push(RayError {
                msg: format!(
                    "`*mut` references are not allowed in struct fields (field `{}`)",
                    field.value.path
                ),
                src: vec![Source {
                    span: parsed_ty.span().copied(),
                    filepath: filepath.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Type,
                context: Some("struct field validation".to_string()),
            });
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

    let impl_definition = impl_def(db, DefTarget::Workspace(def_id));
    let Some(impl_definition) = impl_definition.deref() else {
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
    validate_annotation_policy(&func.sig, filepath, srcmap, errors);
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
                validate_annotation_policy(&func.sig, filepath, srcmap, errors);
                validate_qualifiers(db, &func.sig, file_id, filepath, errors);
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
    validate_qualifiers(db, sig, file_id, filepath, errors);
}

// ============================================================================
// Static cycle prevention (§9 of references.md)
// ============================================================================

/// Build a directed graph of strong reference edges between struct types.
///
/// Nodes are struct `ItemPath`s. An edge A → B exists when struct A has a
/// field of type `*B` (strong shared reference). `id *T` (weak) and value
/// types do not produce edges.
///
/// This is a workspace-level query — cached once and shared by all
/// per-def cycle validation calls.
#[query]
pub fn strong_ref_type_graph(db: &Database, _key: ()) -> Arc<DirectedGraph<ItemPath>> {
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let mut graph = DirectedGraph::new();

    for file_id in workspace.all_file_ids() {
        let file_result = file_ast(db, file_id);

        for def_header in &file_result.defs {
            if !matches!(def_header.kind, DefKind::Struct) {
                continue;
            }

            let target = DefTarget::Workspace(def_header.def_id);
            let Some(sdef) = struct_def(db, target) else {
                continue;
            };

            graph.add_node(sdef.path.clone());

            for field in &sdef.fields {
                for pointee_path in strong_ref_targets(field.ty.mono()) {
                    graph.add_edge(sdef.path.clone(), pointee_path);
                }
            }
        }
    }

    Arc::new(graph)
}

/// Extract the struct `ItemPath`(s) that a type contributes as strong
/// reference edges in the type graph.
///
/// Only `Ty::Ref(inner)` where `inner` is a named struct type produces
/// an edge. Everything else (weak refs, value types, primitives) is ignored.
fn strong_ref_targets(ty: &Ty) -> Vec<ItemPath> {
    match ty {
        Ty::Ref(inner) => match inner.as_ref() {
            Ty::Const(path) | Ty::Proj(path, _) => vec![path.clone()],
            _ => vec![],
        },
        _ => vec![],
    }
}

/// Build a directed graph of value-type embedding edges between struct types.
///
/// An edge A → B exists when struct A has a field of type `B` directly
/// (not behind `*T`, `id *T`, or `*mut T`). A cycle in this graph means
/// the types have infinite size.
#[query]
pub fn value_type_graph(db: &Database, _key: ()) -> Arc<DirectedGraph<ItemPath>> {
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let mut graph = DirectedGraph::new();

    for file_id in workspace.all_file_ids() {
        let file_result = file_ast(db, file_id);

        for def_header in &file_result.defs {
            if !matches!(def_header.kind, DefKind::Struct) {
                continue;
            }

            let target = DefTarget::Workspace(def_header.def_id);
            let Some(sdef) = struct_def(db, target) else {
                continue;
            };

            graph.add_node(sdef.path.clone());

            for field in &sdef.fields {
                for target_path in value_type_targets(field.ty.mono()) {
                    graph.add_edge(sdef.path.clone(), target_path);
                }
            }
        }
    }

    Arc::new(graph)
}

/// Extract struct `ItemPath`(s) from a direct value-type field.
///
/// Returns the path when the field type is a named struct type directly
/// (not behind any reference). References (`*T`, `id *T`, `*mut T`) and
/// primitives are ignored — they provide indirection that breaks the cycle.
fn value_type_targets(ty: &Ty) -> Vec<ItemPath> {
    match ty {
        Ty::Const(path) | Ty::Proj(path, _) => vec![path.clone()],
        _ => vec![],
    }
}

/// Validate a struct definition for participation in a value-type cycle
/// (infinite-size type).
///
/// Returns errors if the struct belongs to an SCC of size > 1 in the
/// value-type graph, or if it directly contains itself as a value field.
#[query]
pub fn validate_value_type_cycles(db: &Database, def_id: DefId) -> Vec<RayError> {
    let file_result = file_ast(db, def_id.file);

    let Some(def_header) = file_result.defs.iter().find(|h| h.def_id == def_id) else {
        return vec![];
    };

    if !matches!(def_header.kind, DefKind::Struct) {
        return vec![];
    }

    let target = DefTarget::Workspace(def_id);
    let Some(sdef) = struct_def(db, target) else {
        return vec![];
    };

    let graph = value_type_graph(db, ());
    let sccs = graph.compute_sccs();

    let Some(scc) = sccs.iter().find(|scc| scc.contains(&sdef.path)) else {
        return vec![];
    };

    let has_self_edge = graph
        .edges
        .get(&sdef.path)
        .map(|targets| targets.contains(&sdef.path))
        .unwrap_or(false);

    if scc.len() <= 1 && !has_self_edge {
        return vec![];
    }

    let cycle_names: Vec<String> = if has_self_edge && scc.len() <= 1 {
        vec![
            sdef.path.item_name().unwrap_or("?").to_string(),
            sdef.path.item_name().unwrap_or("?").to_string(),
        ]
    } else {
        build_cycle_chain(&sdef.path, scc, &graph)
    };

    let chain_str = cycle_names.join(" -> ");

    let filepath = file_result.ast.filepath.clone();
    let (field_sources, suggestion) = collect_cycle_field_sources(
        &file_result.ast.decls,
        def_header.root_node,
        &file_result.source_map,
        &filepath,
        scc,
        &sdef.path,
        &graph,
        value_type_targets,
    );

    let src = if field_sources.is_empty() {
        let span = file_result.source_map.get_by_id(def_header.root_node);
        vec![span.unwrap_or_else(|| Source::from(filepath))]
    } else {
        field_sources
    };

    let hint = match suggestion {
        Some((field, ty)) => format!("Change field `{field}` to `*{ty}` to add indirection"),
        None => "Use `*T` to add indirection".to_string(),
    };

    vec![RayError {
        msg: format!(
            "struct has infinite size due to recursive value-type fields: {chain_str}. {hint}"
        ),
        src,
        kind: RayErrorKind::Type,
        context: Some("cycle detection".to_string()),
    }]
}

/// Validate a struct definition for participation in a strong reference cycle.
///
/// Returns errors if the struct belongs to an SCC of size > 1 in the
/// strong-reference type graph, or if it has a self-referential `*T` field.
#[query]
pub fn validate_struct_cycles(db: &Database, def_id: DefId) -> Vec<RayError> {
    let file_result = file_ast(db, def_id.file);

    let Some(def_header) = file_result.defs.iter().find(|h| h.def_id == def_id) else {
        return vec![];
    };

    if !matches!(def_header.kind, DefKind::Struct) {
        return vec![];
    }

    let target = DefTarget::Workspace(def_id);
    let Some(sdef) = struct_def(db, target) else {
        return vec![];
    };

    let graph = strong_ref_type_graph(db, ());
    let sccs = graph.compute_sccs();

    // Find the SCC containing this struct.
    let Some(scc) = sccs.iter().find(|scc| scc.contains(&sdef.path)) else {
        return vec![];
    };

    // Check for self-edge (a struct with a *Self field).
    let has_self_edge = graph
        .edges
        .get(&sdef.path)
        .map(|targets| targets.contains(&sdef.path))
        .unwrap_or(false);

    if scc.len() <= 1 && !has_self_edge {
        return vec![];
    }

    // Build the cycle chain for the error message.
    let cycle_names: Vec<String> = if has_self_edge && scc.len() <= 1 {
        // Self-referential: Foo → Foo
        vec![
            sdef.path.item_name().unwrap_or("?").to_string(),
            sdef.path.item_name().unwrap_or("?").to_string(),
        ]
    } else {
        // Multi-struct cycle: build a chain starting from this struct.
        build_cycle_chain(&sdef.path, scc, &graph)
    };

    let chain_str = cycle_names.join(" -> ");

    // Collect source locations for the offending fields in this struct.
    let filepath = file_result.ast.filepath.clone();
    let (field_sources, suggestion) = collect_cycle_field_sources(
        &file_result.ast.decls,
        def_header.root_node,
        &file_result.source_map,
        &filepath,
        scc,
        &sdef.path,
        &graph,
        strong_ref_targets,
    );

    let src = if field_sources.is_empty() {
        // Fallback: point at the struct declaration itself.
        let span = file_result.source_map.get_by_id(def_header.root_node);
        vec![span.unwrap_or_else(|| Source::from(filepath))]
    } else {
        field_sources
    };

    let hint = match suggestion {
        Some((field, ty)) => {
            format!("Change field `{field}` to `id *{ty}` to break the cycle")
        }
        None => "Break the cycle by changing a field to `id *T`".to_string(),
    };

    vec![RayError {
        msg: format!("cyclic strong references: {chain_str}. {hint}"),
        src,
        kind: RayErrorKind::Type,
        context: Some("cycle detection".to_string()),
    }]
}

/// Build a human-readable cycle chain starting from `start`.
///
/// Follows edges in the graph through SCC members to produce e.g.
/// `["Foo", "Bar", "Baz", "Foo"]`.
fn build_cycle_chain(
    start: &ItemPath,
    scc: &[ItemPath],
    graph: &DirectedGraph<ItemPath>,
) -> Vec<String> {
    let scc_set: HashSet<&ItemPath> = scc.iter().collect();
    let mut chain = vec![start.item_name().unwrap_or("?").to_string()];
    let mut current = start;
    let mut visited: HashSet<&ItemPath> = HashSet::new();
    visited.insert(current);

    loop {
        let Some(targets) = graph.edges.get(current) else {
            break;
        };

        // Follow the first unvisited SCC-member neighbor.
        let next = targets
            .iter()
            .find(|t| scc_set.contains(t) && !visited.contains(t));

        match next {
            Some(n) => {
                chain.push(n.item_name().unwrap_or("?").to_string());
                visited.insert(n);
                current = n;
            }
            None => {
                // All neighbors visited — close the cycle back to start.
                chain.push(start.item_name().unwrap_or("?").to_string());
                break;
            }
        }
    }

    chain
}

/// Collect `Source` entries for fields in this struct that contribute to the
/// cycle. Uses `target_fn` to extract edge targets from each field's AST type,
/// so the same logic works for both strong-ref and value-type cycles.
fn collect_cycle_field_sources(
    decls: &[Node<Decl>],
    root_node: NodeId,
    source_map: &SourceMap,
    filepath: &FilePath,
    scc: &[ItemPath],
    struct_path: &ItemPath,
    graph: &DirectedGraph<ItemPath>,
    target_fn: fn(&Ty) -> Vec<ItemPath>,
) -> (Vec<Source>, Option<(String, String)>) {
    let Some(decl_node) = find_def_ast(decls, root_node) else {
        return (vec![], None);
    };

    let Decl::Struct(st) = &decl_node.value else {
        return (vec![], None);
    };

    let Some(fields) = &st.fields else {
        return (vec![], None);
    };

    let scc_set: HashSet<&ItemPath> = scc.iter().collect();

    // Get the edge targets for this struct.
    let edge_targets: HashSet<&ItemPath> = graph
        .edges
        .get(struct_path)
        .map(|targets| targets.iter().filter(|t| scc_set.contains(t)).collect())
        .unwrap_or_default();

    // Build a set of edge target item names for matching against parsed
    // (unqualified) type paths. The graph uses fully-qualified ItemPaths but
    // parsed field types use unqualified names.
    let edge_target_names: HashSet<Option<&str>> =
        edge_targets.iter().map(|t| t.item_name()).collect();

    let mut sources = Vec::new();
    let mut first_suggestion: Option<(String, String)> = None;

    for field_node in fields {
        let Some(parsed_ty) = &field_node.value.ty else {
            continue;
        };

        // Check if this field's type contributes an edge to an SCC member.
        let targets = target_fn(&parsed_ty.value().ty);
        for target_path in &targets {
            let matches_edge = edge_targets.contains(target_path)
                || edge_target_names.contains(&target_path.item_name());
            if matches_edge {
                // Capture the first offending field for the suggestion.
                if first_suggestion.is_none() {
                    let field_name = field_node
                        .value
                        .path
                        .name()
                        .unwrap_or_else(|| "?".to_string());
                    let type_name = target_path.item_name().unwrap_or("T").to_string();
                    first_suggestion = Some((field_name, type_name));
                }

                if let Some(src) = source_map.get_by_id(field_node.id) {
                    sources.push(src);
                } else {
                    sources.push(Source {
                        span: parsed_ty.span().copied(),
                        filepath: filepath.clone(),
                        ..Default::default()
                    });
                }
            }
        }
    }

    (sources, first_suggestion)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::pathlib::{FilePath, ModulePath};

    use ray_shared::def::DefKind;

    use crate::{
        queries::{
            defs::impls_in_module,
            diagnostics::file_diagnostics,
            libraries::LoadedLibraries,
            parse::parse_file,
            validation::{
                strong_ref_type_graph, validate_def, validate_struct_cycles,
                validate_value_type_cycles, value_type_graph,
            },
            workspace::{CompilerOptions, FileMetadata, FileSource, WorkspaceSnapshot},
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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
    fn validate_def_no_error_for_missing_return_with_block_body() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Block body with annotated params but no return type is allowed.
        // The return type is implicitly () (ImplicitUnit status).
        FileSource::new(&db, file_id, r#"fn ok(x: int) { x * 2 }"#.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let ok_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "ok")
            .expect("should find ok function");

        let errors = validate_def(&db, ok_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no validation error for block body with implicit unit return, got: {:?}",
            errors
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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
    fn new(x: int, y: int) -> Point => Point { x, y }
}
"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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

    #[test]
    fn validate_def_no_error_for_tuple_destructuring() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"fn foo() -> int {
            a, b = (1, 2)
            a
        }"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo function");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for tuple destructuring, got: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_no_error_for_tuple_destructuring_with_discard() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"fn foo() -> int {
            _, b = (1, 2)
            b
        }"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo function");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for tuple destructuring with discard, got: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_error_for_reassign_tuple_to_immutable() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // a and b are immutable from the first assignment, second should error
        let source = r#"fn foo() -> int {
            a, b = (1, 2)
            a, b = (3, 4)
            a
        }"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo function");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected errors for reassignment to immutable tuple bindings"
        );
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("cannot assign to immutable")),
            "Error should mention immutable assignment: {:?}",
            errors
        );
    }

    // ====================================================================
    // Struct field validation tests
    // ====================================================================

    #[test]
    fn validate_def_error_for_mut_ref_in_struct_field() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"struct Foo { x: *mut int }"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "Foo")
            .expect("should find Foo struct");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for *mut ref in struct field"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("*mut")),
            "Error should mention *mut: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_ok_for_shared_and_id_ref_in_struct_fields() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"struct Foo { x: *int, y: id *int }"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "Foo")
            .expect("should find Foo struct");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for *T and id *T in struct fields, got: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_error_for_nested_mut_ref_in_struct_field() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // *(*mut int) contains *mut, so this should error
        let source = r#"struct Foo { x: *(*mut int) }"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "Foo")
            .expect("should find Foo struct");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for nested *mut ref in struct field"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("*mut")),
            "Error should mention *mut: {:?}",
            errors
        );
    }

    // ====================================================================
    // Universal type annotation validation tests (id *mut T rejection)
    // ====================================================================

    #[test]
    fn validate_def_error_for_id_mut_ref_in_function_param() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // `id **mut int` parses as IdRef(MutRef(int)) — invalid nesting.
        // The first `*` is part of the `id *` prefix, the second `*mut` is the pointee.
        let source = r#"fn bad(x: id **mut int) -> int { x }"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let bad_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "bad")
            .expect("should find bad function");

        let errors = validate_def(&db, bad_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for id **mut T in function parameter"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("cannot wrap")
                && e.context.as_deref() == Some("type annotation validation")),
            "Error should be from type annotation validation: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_error_for_id_mut_ref_in_return_type() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"fn bad(x: int) -> id **mut int { x }"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let bad_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "bad")
            .expect("should find bad function");

        let errors = validate_def(&db, bad_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for id **mut T in return type"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("cannot wrap")),
            "Error should mention invalid ref nesting: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_error_for_id_mut_ref_in_struct_field() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // id **mut T is caught by universal type annotation validation
        let source = r#"struct Foo { x: id **mut int }"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "Foo")
            .expect("should find Foo struct");

        let errors = validate_def(&db, foo_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for id **mut T in struct field"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("cannot wrap")),
            "Error should mention invalid ref nesting: {:?}",
            errors
        );
    }

    #[test]
    fn validate_def_no_error_for_valid_ref_types_in_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // All three reference kinds are valid individually
        let source = r#"fn ok(x: *mut int, y: *int, z: id *int) -> *int { y }"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let ok_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "ok")
            .expect("should find ok function");

        let errors = validate_def(&db, ok_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for valid reference types, got: {:?}",
            errors
        );
    }

    // ====================================================================
    // Static cycle prevention tests
    // ====================================================================

    /// Set up a no-core test database (cycle detection doesn't need the core library).
    fn setup_cycle_db(source: &str) -> (Database, ray_shared::file_id::FileId) {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
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
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );
        (db, file_id)
    }

    #[test]
    fn cycle_no_error_for_acyclic_refs() {
        let source = r#"
struct Bar {}
struct Foo { bar: *Bar }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        for def in &parse_result.defs {
            if matches!(def.kind, DefKind::Struct) {
                let errors = validate_struct_cycles(&db, def.def_id);
                assert!(
                    errors.is_empty(),
                    "Acyclic refs should produce no cycle error for {}, got: {:?}",
                    def.name,
                    errors
                );
            }
        }
    }

    #[test]
    fn cycle_error_for_mutual_strong_refs() {
        let source = r#"
struct Foo { bar: *Bar }
struct Bar { foo: *Foo }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        let foo = parse_result.defs.iter().find(|d| d.name == "Foo").unwrap();
        let bar = parse_result.defs.iter().find(|d| d.name == "Bar").unwrap();

        let foo_errors = validate_struct_cycles(&db, foo.def_id);
        assert!(!foo_errors.is_empty(), "Foo should have a cycle error");
        assert!(
            foo_errors[0].msg.contains("cyclic strong references"),
            "Error should mention cyclic strong references: {}",
            foo_errors[0].msg
        );
        assert!(
            foo_errors[0]
                .msg
                .contains("Change field `bar` to `id *Bar`"),
            "Error should suggest specific field change: {}",
            foo_errors[0].msg
        );
        assert_eq!(
            foo_errors[0].context.as_deref(),
            Some("cycle detection"),
            "Error context should be 'cycle detection'"
        );

        let bar_errors = validate_struct_cycles(&db, bar.def_id);
        assert!(!bar_errors.is_empty(), "Bar should have a cycle error");
    }

    #[test]
    fn cycle_error_for_self_referential_struct() {
        let source = r#"
struct Node { next: *Node }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        let node = parse_result.defs.iter().find(|d| d.name == "Node").unwrap();

        let errors = validate_struct_cycles(&db, node.def_id);
        assert!(
            !errors.is_empty(),
            "Self-referential struct should have a cycle error"
        );
        assert!(
            errors[0].msg.contains("Node"),
            "Error should mention Node: {}",
            errors[0].msg
        );
    }

    #[test]
    fn cycle_no_error_when_weak_ref_breaks_cycle() {
        let source = r#"
struct Foo { bar: *Bar }
struct Bar { foo: id *Foo }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        for def in &parse_result.defs {
            if matches!(def.kind, DefKind::Struct) {
                let errors = validate_struct_cycles(&db, def.def_id);
                assert!(
                    errors.is_empty(),
                    "Weak ref should break cycle for {}, got: {:?}",
                    def.name,
                    errors
                );
            }
        }
    }

    #[test]
    fn cycle_error_for_transitive_three_struct_cycle() {
        let source = r#"
struct A { b: *B }
struct B { c: *C }
struct C { a: *A }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        // All three structs should report cycle errors.
        for def in &parse_result.defs {
            if matches!(def.kind, DefKind::Struct) {
                let errors = validate_struct_cycles(&db, def.def_id);
                assert!(
                    !errors.is_empty(),
                    "Struct {} should have a cycle error",
                    def.name
                );
            }
        }
    }

    #[test]
    fn cycle_no_error_for_value_type_fields() {
        // Value-type fields (not behind *T) don't create edges.
        let source = r#"
struct Inner { x: int }
struct Outer { inner: Inner, y: int }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        for def in &parse_result.defs {
            if matches!(def.kind, DefKind::Struct) {
                let errors = validate_struct_cycles(&db, def.def_id);
                assert!(
                    errors.is_empty(),
                    "Value-type fields should not produce cycle errors for {}, got: {:?}",
                    def.name,
                    errors
                );
            }
        }
    }

    #[test]
    fn cycle_no_error_for_non_struct_defs() {
        let source = r#"
fn foo() -> int => 42
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        let foo = parse_result.defs.iter().find(|d| d.name == "foo").unwrap();

        let errors = validate_struct_cycles(&db, foo.def_id);
        assert!(
            errors.is_empty(),
            "Non-struct defs should return no cycle errors"
        );
    }

    #[test]
    fn cycle_error_has_field_source_locations() {
        let source = r#"
struct Foo { bar: *Bar }
struct Bar { foo: *Foo }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        let foo = parse_result.defs.iter().find(|d| d.name == "Foo").unwrap();

        let errors = validate_struct_cycles(&db, foo.def_id);
        assert!(!errors.is_empty());

        // The error should have source location(s) pointing at the offending field.
        assert!(
            !errors[0].src.is_empty(),
            "Cycle error should have source locations"
        );
        assert!(
            errors[0].src[0].span.is_some(),
            "Source location should have a span"
        );
    }

    #[test]
    fn cycle_graph_has_correct_structure() {
        let source = r#"
struct Foo { bar: *Bar, weak: id *Baz }
struct Bar { x: int }
struct Baz {}
"#;
        let (db, _file_id) = setup_cycle_db(source);
        let graph = strong_ref_type_graph(&db, ());

        // Foo should have an edge to Bar (strong ref) but NOT to Baz (weak ref).
        let foo_path = ray_shared::pathlib::ItemPath::from("test::Foo");
        let bar_path = ray_shared::pathlib::ItemPath::from("test::Bar");
        let baz_path = ray_shared::pathlib::ItemPath::from("test::Baz");

        let foo_targets = graph.edges.get(&foo_path).expect("Foo should be in graph");
        assert!(
            foo_targets.contains(&bar_path),
            "Foo should have edge to Bar"
        );
        assert!(
            !foo_targets.contains(&baz_path),
            "Foo should NOT have edge to Baz (id *T is weak)"
        );

        // Bar should have no outgoing edges (x: int is a value type).
        let bar_targets = graph.edges.get(&bar_path).expect("Bar should be in graph");
        assert!(bar_targets.is_empty(), "Bar should have no outgoing edges");
    }

    #[test]
    fn cycle_mixed_strong_and_weak_fields() {
        // Foo → *Bar (strong), Foo → id *Baz (weak)
        // Bar → *Foo (strong) — cycle between Foo and Bar
        // Baz → *Foo (strong) — no cycle since Foo → Baz is weak
        let source = r#"
struct Foo { bar: *Bar, baz: id *Baz }
struct Bar { foo: *Foo }
struct Baz { foo: *Foo }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        let foo = parse_result.defs.iter().find(|d| d.name == "Foo").unwrap();
        let bar = parse_result.defs.iter().find(|d| d.name == "Bar").unwrap();
        let baz = parse_result.defs.iter().find(|d| d.name == "Baz").unwrap();

        // Foo and Bar are in a cycle.
        assert!(
            !validate_struct_cycles(&db, foo.def_id).is_empty(),
            "Foo should have cycle error (Foo <-> Bar)"
        );
        assert!(
            !validate_struct_cycles(&db, bar.def_id).is_empty(),
            "Bar should have cycle error (Foo <-> Bar)"
        );

        // Baz is NOT in a cycle: Baz → *Foo is a one-way edge, and
        // Foo → id *Baz is weak (not counted).
        assert!(
            validate_struct_cycles(&db, baz.def_id).is_empty(),
            "Baz should NOT have a cycle error (Foo -> Baz is weak)"
        );
    }

    #[test]
    fn cycle_diagnostics_integration() {
        // Cycle errors should appear in file_diagnostics.
        let source = r#"
struct Foo { bar: *Bar }
struct Bar { foo: *Foo }
"#;
        let (db, file_id) = setup_cycle_db(source);

        let errors = file_diagnostics(&db, file_id);

        let cycle_errors: Vec<_> = errors
            .iter()
            .filter(|e| e.context.as_deref() == Some("cycle detection"))
            .collect();

        assert_eq!(
            cycle_errors.len(),
            2,
            "Should have 2 cycle errors (one per struct), got: {:?}",
            cycle_errors
        );
    }

    #[test]
    fn cycle_no_error_for_struct_with_only_value_and_weak_fields() {
        let source = r#"
struct Foo { x: int, parent: id *Foo }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        let foo = parse_result.defs.iter().find(|d| d.name == "Foo").unwrap();

        let errors = validate_struct_cycles(&db, foo.def_id);
        assert!(
            errors.is_empty(),
            "id *Foo self-reference should not be a cycle error, got: {:?}",
            errors
        );
    }

    // ====================================================================
    // Value-type cycle tests (infinite-size types)
    // ====================================================================

    #[test]
    fn value_cycle_error_for_mutual_embedding() {
        let source = r#"
struct Foo { bar: Bar }
struct Bar { foo: Foo }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        let foo = parse_result.defs.iter().find(|d| d.name == "Foo").unwrap();
        let bar = parse_result.defs.iter().find(|d| d.name == "Bar").unwrap();

        let foo_errors = validate_value_type_cycles(&db, foo.def_id);
        assert!(
            !foo_errors.is_empty(),
            "Foo should have a value-type cycle error"
        );
        assert!(
            foo_errors[0].msg.contains("infinite size"),
            "Error should mention infinite size: {}",
            foo_errors[0].msg
        );
        assert!(
            foo_errors[0].msg.contains("Change field `bar` to `*Bar`"),
            "Error should suggest specific field change: {}",
            foo_errors[0].msg
        );
        assert_eq!(foo_errors[0].context.as_deref(), Some("cycle detection"),);

        let bar_errors = validate_value_type_cycles(&db, bar.def_id);
        assert!(
            !bar_errors.is_empty(),
            "Bar should have a value-type cycle error"
        );
    }

    #[test]
    fn value_cycle_error_for_self_embedding() {
        let source = r#"
struct Node { child: Node }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        let node = parse_result.defs.iter().find(|d| d.name == "Node").unwrap();

        let errors = validate_value_type_cycles(&db, node.def_id);
        assert!(
            !errors.is_empty(),
            "Self-embedding struct should have an infinite-size error"
        );
        assert!(
            errors[0].msg.contains("Node"),
            "Error should mention Node: {}",
            errors[0].msg
        );
    }

    #[test]
    fn value_cycle_no_error_for_ref_indirection() {
        // Using *T breaks the value-type cycle.
        let source = r#"
struct Foo { bar: *Bar }
struct Bar { foo: *Foo }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        for def in &parse_result.defs {
            if matches!(def.kind, DefKind::Struct) {
                let errors = validate_value_type_cycles(&db, def.def_id);
                assert!(
                    errors.is_empty(),
                    "*T indirection should prevent value-type cycle for {}, got: {:?}",
                    def.name,
                    errors
                );
            }
        }
    }

    #[test]
    fn value_cycle_no_error_for_acyclic_embedding() {
        let source = r#"
struct Inner { x: int }
struct Outer { inner: Inner }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        for def in &parse_result.defs {
            if matches!(def.kind, DefKind::Struct) {
                let errors = validate_value_type_cycles(&db, def.def_id);
                assert!(
                    errors.is_empty(),
                    "Acyclic value embedding should not produce errors for {}, got: {:?}",
                    def.name,
                    errors
                );
            }
        }
    }

    #[test]
    fn value_cycle_error_for_transitive_chain() {
        let source = r#"
struct A { b: B }
struct B { c: C }
struct C { a: A }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        for def in &parse_result.defs {
            if matches!(def.kind, DefKind::Struct) {
                let errors = validate_value_type_cycles(&db, def.def_id);
                assert!(
                    !errors.is_empty(),
                    "Struct {} should have an infinite-size error",
                    def.name
                );
            }
        }
    }

    #[test]
    fn value_cycle_graph_has_correct_structure() {
        let source = r#"
struct Foo { bar: Bar, ref_baz: *Baz }
struct Bar { x: int }
struct Baz {}
"#;
        let (db, _file_id) = setup_cycle_db(source);
        let graph = value_type_graph(&db, ());

        let foo_path = ray_shared::pathlib::ItemPath::from("test::Foo");
        let bar_path = ray_shared::pathlib::ItemPath::from("test::Bar");
        let baz_path = ray_shared::pathlib::ItemPath::from("test::Baz");

        let foo_targets = graph.edges.get(&foo_path).expect("Foo should be in graph");
        assert!(
            foo_targets.contains(&bar_path),
            "Foo should have value-type edge to Bar"
        );
        assert!(
            !foo_targets.contains(&baz_path),
            "Foo should NOT have edge to Baz (*T is indirection, not value embedding)"
        );
    }

    #[test]
    fn value_cycle_no_error_for_non_struct_defs() {
        let source = r#"
fn foo() -> int => 42
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        let foo = parse_result.defs.iter().find(|d| d.name == "foo").unwrap();

        let errors = validate_value_type_cycles(&db, foo.def_id);
        assert!(
            errors.is_empty(),
            "Non-struct defs should return no value-type cycle errors"
        );
    }

    #[test]
    fn value_cycle_diagnostics_integration() {
        let source = r#"
struct Foo { bar: Bar }
struct Bar { foo: Foo }
"#;
        let (db, file_id) = setup_cycle_db(source);

        let errors = file_diagnostics(&db, file_id);

        let value_cycle_errors: Vec<_> = errors
            .iter()
            .filter(|e| {
                e.context.as_deref() == Some("cycle detection") && e.msg.contains("infinite size")
            })
            .collect();

        assert_eq!(
            value_cycle_errors.len(),
            2,
            "Should have 2 value-type cycle errors (one per struct), got: {:?}",
            value_cycle_errors
        );
    }

    #[test]
    fn value_cycle_partial_indirection_breaks_cycle() {
        // Foo embeds Bar directly, but Bar uses *Foo — breaks the value cycle.
        let source = r#"
struct Foo { bar: Bar }
struct Bar { foo: *Foo }
"#;
        let (db, file_id) = setup_cycle_db(source);
        let parse_result = parse_file(&db, file_id);

        for def in &parse_result.defs {
            if matches!(def.kind, DefKind::Struct) {
                let errors = validate_value_type_cycles(&db, def.def_id);
                assert!(
                    errors.is_empty(),
                    "Partial *T indirection should break value-type cycle for {}, got: {:?}",
                    def.name,
                    errors
                );
            }
        }
    }
}

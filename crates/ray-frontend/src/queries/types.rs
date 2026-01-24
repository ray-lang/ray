//! Type mapping queries for the incremental compiler.

use std::collections::HashMap;

use ray_core::ast::{Decl, Expr, Func, FuncSig, Impl, Node, Struct, Trait};
use ray_query_macros::query;
use ray_shared::{
    def::{DefId, SignatureStatus},
    node_id::NodeId,
    ty::{
        SchemaVarAllocator, Ty, TyVar,
        map_vars::{MapVars, MappingState},
    },
};
use ray_typing::{
    constraints::Predicate,
    types::{Subst, Substitutable, TyScheme},
};

use crate::{
    queries::transform::file_ast,
    query::{Database, Query},
};

/// Result of mapping type variables in a definition's type annotations.
///
/// Contains bidirectional mappings between user-written type variables (e.g., `'a`, `T`)
/// and schema variables (e.g., `?s:hash:0`, `?s:hash:1`).
///
/// This is used by downstream queries like `annotated_scheme` to consistently
/// map user type variables to schema variables for typechecking.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MappedDefTypes {
    /// Forward mapping: user type variable -> schema variable
    pub var_map: HashMap<TyVar, TyVar>,
    /// Reverse mapping: schema variable -> user type variable (for pretty printing)
    pub reverse_map: HashMap<TyVar, TyVar>,
}

impl MappedDefTypes {
    /// Convert the forward variable mapping of user type variables
    /// to schema variables into a Subst map.
    pub fn var_map_subst(&self) -> Subst {
        Subst::from(&self.var_map)
    }

    /// Convert the reverse variable mapping of schema variables to
    /// user type variables into a Subst map.
    pub fn reverse_map_subst(&self) -> Subst {
        Subst::from(&self.reverse_map)
    }
}

/// Map type variables in a definition's type annotations to fresh schema variables.
///
/// This query extracts all type annotations from a definition and maps any
/// user-written type variables (e.g., `'a`, `T`) to fresh schema variables
/// (e.g., `?s0`, `?s1`).
///
/// # Arguments
///
/// * `db` - The query database
/// * `def_id` - The definition to analyze
///
/// # Returns
///
/// A `MappedDefTypes` containing:
/// - `var_map`: Forward mapping from user vars to schema vars
/// - `reverse_map`: Reverse mapping for pretty printing
/// - `types`: Mapped types indexed by their AST NodeId
#[query]
pub fn mapped_def_types(db: &Database, def_id: DefId) -> MappedDefTypes {
    let file_result = file_ast(db, def_id.file);

    // Find the DefHeader for this definition
    let def_header = match file_result.defs.iter().find(|h| h.def_id == def_id) {
        Some(header) => header,
        None => return MappedDefTypes::default(),
    };

    // Find the AST node for this definition
    let def_ast = match find_def_ast(&file_result.ast.decls, def_header.root_node) {
        Some(ast) => ast,
        None => return MappedDefTypes::default(),
    };

    // Extract and map type annotations based on definition kind
    extract_and_map_types(def_id, def_ast)
}

/// Determine the annotation status of a definition's signature.
///
/// This query determines whether a definition has:
/// - `FullyAnnotated`: All parameter and return types explicit
/// - `ReturnElided`: Parameters annotated, return type inferred from => body
/// - `Unannotated`: Missing parameter or return type annotations
///
/// Non-function definitions (structs, traits, impls, type aliases) are always
/// considered `FullyAnnotated` since they require explicit type information.
#[query]
pub fn def_signature_status(db: &Database, def_id: DefId) -> SignatureStatus {
    let file_result = file_ast(db, def_id.file);

    // Find the DefHeader for this definition
    let def_header = match file_result.defs.iter().find(|h| h.def_id == def_id) {
        Some(header) => header,
        None => return SignatureStatus::Unannotated,
    };

    // Find the AST node for this definition
    let def_ast = match find_def_ast(&file_result.ast.decls, def_header.root_node) {
        Some(ast) => ast,
        None => return SignatureStatus::Unannotated,
    };

    compute_signature_status(def_ast)
}

/// Compute the signature status for a declaration.
fn compute_signature_status(decl: &Node<Decl>) -> SignatureStatus {
    match &decl.value {
        Decl::Func(func) => compute_func_signature_status(func),
        Decl::FnSig(sig) => compute_fn_sig_signature_status(sig),
        Decl::Extern(ext) => compute_signature_status(ext.decl_node()),
        // These always have explicit type information
        Decl::Struct(_) | Decl::Trait(_) | Decl::Impl(_) | Decl::TypeAlias(_, _) => {
            SignatureStatus::FullyAnnotated
        }
        // Variable declarations
        Decl::Name(name) | Decl::Mutable(name) => {
            if name.value.ty.is_some() {
                SignatureStatus::FullyAnnotated
            } else {
                SignatureStatus::Unannotated
            }
        }
        Decl::Declare(assign) => {
            // A declaration has an explicit type if the LHS has a type annotation
            if assign.is_annotated() {
                SignatureStatus::FullyAnnotated
            } else {
                SignatureStatus::Unannotated
            }
        }
    }
}

/// Compute signature status for a function.
fn compute_func_signature_status(func: &Func) -> SignatureStatus {
    // Check if all parameters have type annotations
    let all_params_annotated = func.sig.params.iter().all(|p| p.value.ty().is_some());
    if !all_params_annotated {
        return SignatureStatus::Unannotated;
    }

    // All params are annotated, check return type
    if func.sig.ret_ty.is_some() {
        return SignatureStatus::FullyAnnotated;
    }

    // Check if body is an arrow expression (not a block)
    // Arrow body: fn foo(x: int) => x + 1  -> ReturnElided
    // Block body: fn foo(x: int) { x + 1 } -> Unannotated
    let body_is_block = func
        .body
        .as_ref()
        .map(|b| matches!(b.value, Expr::Block(_)))
        .unwrap_or(true); // No body = treat as block (unannotated)

    if body_is_block {
        SignatureStatus::Unannotated
    } else {
        SignatureStatus::ReturnElided
    }
}

/// Compute signature status for a standalone function signature (trait method).
fn compute_fn_sig_signature_status(sig: &FuncSig) -> SignatureStatus {
    // Check if all parameters have type annotations
    let all_params_annotated = sig.params.iter().all(|p| p.value.ty().is_some());
    if !all_params_annotated {
        return SignatureStatus::Unannotated;
    }

    // Check return type
    if sig.ret_ty.is_some() {
        SignatureStatus::FullyAnnotated
    } else {
        // For standalone signatures without bodies, missing return type = unannotated
        SignatureStatus::Unannotated
    }
}

/// Compute the type scheme for an annotated definition.
///
/// Returns `None` if the definition is `Unannotated` and requires type inference.
/// For `FullyAnnotated` definitions, returns the scheme built from explicit annotations.
/// For `ReturnElided` definitions, returns a scheme with a placeholder return type.
///
/// # Arguments
///
/// * `db` - The query database
/// * `def_id` - The definition to analyze
///
/// # Returns
///
/// `Some(TyScheme)` if the definition has sufficient annotations, `None` otherwise.
#[query]
pub fn annotated_scheme(db: &Database, def_id: DefId) -> Option<TyScheme> {
    let status = def_signature_status(db, def_id);
    if status == SignatureStatus::Unannotated {
        return None;
    }

    let file_result = file_ast(db, def_id.file);
    let mapping = mapped_def_types(db, def_id);

    // Find the DefHeader for this definition
    let def_header = file_result.defs.iter().find(|h| h.def_id == def_id)?;

    // Find the AST node for this definition
    let def_ast = find_def_ast(&file_result.ast.decls, def_header.root_node)?;

    compute_scheme(def_ast, &mapping, status)
}

/// Compute the type scheme for a declaration with the given mapping state.
fn compute_scheme(
    decl: &Node<Decl>,
    mapping: &MappedDefTypes,
    status: SignatureStatus,
) -> Option<TyScheme> {
    match &decl.value {
        Decl::Func(func) => compute_func_scheme(&func.sig, mapping, status),
        Decl::FnSig(sig) => compute_func_scheme(sig, mapping, status),
        Decl::Extern(ext) => compute_scheme(ext.decl_node(), mapping, status),
        // For non-function definitions, we don't compute schemes here
        // (structs/traits/impls have their own type representations)
        _ => None,
    }
}

/// Compute the type scheme for a function signature.
fn compute_func_scheme(
    sig: &FuncSig,
    mapping: &MappedDefTypes,
    status: SignatureStatus,
) -> Option<TyScheme> {
    let var_map = mapping.var_map_subst();

    // Extract and map parameter types
    let mut param_tys = Vec::with_capacity(sig.params.len());
    for param in &sig.params {
        let mut ty = param.value.ty()?.clone();
        ty.apply_subst(&var_map);
        param_tys.push(ty);
    }

    // Extract return type
    let ret_ty = if let Some(parsed_ty) = &sig.ret_ty {
        let mut ty = parsed_ty.clone_value();
        ty.apply_subst(&var_map);
        ty
    } else if status == SignatureStatus::ReturnElided {
        // For arrow bodies, use a return placeholder
        Ty::ret_placeholder(&sig.path.value)
    } else {
        // No return type annotation and not elided - shouldn't happen for annotated
        Ty::unit()
    };

    // Build the function type
    let func_ty = Ty::Func(param_tys, Box::new(ret_ty));

    // Extract qualifiers (where clauses) and convert to predicates
    let mut predicates = Vec::with_capacity(sig.qualifiers.len());
    for qual in &sig.qualifiers {
        let mut qual_ty = qual.clone_value();
        qual_ty.apply_subst(&var_map);

        // Convert Ty::Proj to Predicate::Class
        if let Some(pred) = ty_to_predicate(&qual_ty) {
            predicates.push(pred);
        }
    }

    // Collect type variables (schema vars) from the mapped types
    let mut vars: Vec<TyVar> = mapping.var_map.values().cloned().collect();
    vars.sort();
    vars.dedup();

    // Build the scheme
    let scheme = if vars.is_empty() && predicates.is_empty() {
        TyScheme::from_mono(func_ty)
    } else {
        TyScheme::new(vars, predicates, func_ty)
    };

    Some(scheme)
}

/// Convert a type to a predicate (for where clauses).
fn ty_to_predicate(ty: &Ty) -> Option<Predicate> {
    match ty {
        Ty::Proj(path, args) => {
            let name = path.to_string();
            Some(Predicate::class(name, args.clone()))
        }
        Ty::Const(path) => {
            let name = path.to_string();
            Some(Predicate::class(name, vec![]))
        }
        _ => None,
    }
}

/// Extract type annotations from a declaration and build the type variable mappings.
fn extract_and_map_types(def_id: DefId, decl: &Node<Decl>) -> MappedDefTypes {
    let mut allocator = SchemaVarAllocator::with_def_scope(def_id);
    let mut state = MappingState::default();

    match &decl.value {
        Decl::Func(func) => {
            map_func_sig_vars(&func.sig, &mut state, &mut allocator);
        }
        Decl::FnSig(sig) => {
            map_func_sig_vars(sig, &mut state, &mut allocator);
        }
        Decl::Struct(st) => {
            map_struct_vars(st, &mut state, &mut allocator);
        }
        Decl::Trait(tr) => {
            map_trait_vars(tr, &mut state, &mut allocator);
        }
        Decl::TypeAlias(_name, parsed_ty) => {
            let ty = parsed_ty.clone_value();
            let (_, new_state) = ty.map_vars(&state, &mut allocator);
            state = new_state;
        }
        Decl::Impl(im) => {
            map_impl_vars(im, &mut state, &mut allocator);
        }
        Decl::Extern(ext) => {
            // Extern wraps another declaration, recurse into it
            return extract_and_map_types(def_id, ext.decl_node());
        }
        // Name, Mutable, Declare don't have type annotations that need mapping
        Decl::Name(_) | Decl::Mutable(_) | Decl::Declare(_) => {}
    }

    MappedDefTypes {
        var_map: state.forward_map,
        reverse_map: state.reverse_map,
    }
}

/// Map type variables in a function signature to schema variables.
fn map_func_sig_vars(sig: &FuncSig, state: &mut MappingState, allocator: &mut SchemaVarAllocator) {
    // Map parameter types
    for param in &sig.params {
        if let Some(ty) = param.value.ty() {
            let (_, new_state) = ty.clone().map_vars(state, allocator);
            *state = new_state;
        }
    }

    // Map return type if present
    if let Some(parsed_ty) = &sig.ret_ty {
        if parsed_ty.span().is_some() {
            let ty = parsed_ty.clone_value();
            let (_, new_state) = ty.map_vars(state, allocator);
            *state = new_state;
        }
    }

    // Map qualifier types (where clauses)
    for qual in &sig.qualifiers {
        let ty = qual.clone_value();
        let (_, new_state) = ty.map_vars(state, allocator);
        *state = new_state;
    }
}

/// Map type variables in a struct definition to schema variables.
fn map_struct_vars(st: &Struct, state: &mut MappingState, allocator: &mut SchemaVarAllocator) {
    // Map field types
    if let Some(fields) = &st.fields {
        for field in fields {
            if let Some(parsed_ty) = &field.value.ty {
                let ty = parsed_ty.clone_value().mono().clone();
                let (_, new_state) = ty.map_vars(state, allocator);
                *state = new_state;
            }
        }
    }
}

/// Map type variables in a trait definition to schema variables.
fn map_trait_vars(tr: &Trait, state: &mut MappingState, allocator: &mut SchemaVarAllocator) {
    // Map the trait's self type
    let ty = tr.ty.clone_value();
    let (_, new_state) = ty.map_vars(state, allocator);
    *state = new_state;

    // Map super trait if present
    if let Some(super_trait) = &tr.super_trait {
        let ty = super_trait.clone_value();
        let (_, new_state) = ty.map_vars(state, allocator);
        *state = new_state;
    }
}

/// Map type variables in an impl block to schema variables.
fn map_impl_vars(im: &Impl, state: &mut MappingState, allocator: &mut SchemaVarAllocator) {
    // Map the impl's target type
    let ty = im.ty.clone_value();
    let (_, new_state) = ty.map_vars(state, allocator);
    *state = new_state;

    // Map qualifier types
    for qual in &im.qualifiers {
        let ty = qual.clone_value();
        let (_, new_state) = ty.map_vars(state, allocator);
        *state = new_state;
    }
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
            // Check function declarations
            if let Some(funcs) = &im.funcs {
                for func in funcs {
                    if func.id == root_node {
                        // funcs is Vec<Node<Func>>, not Vec<Node<Decl>>
                        // This case is handled differently - impl methods are found via their own DefId
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
    use ray_shared::{
        def::SignatureStatus,
        pathlib::{FilePath, ModulePath},
    };

    use crate::{
        queries::{
            libraries::LoadedLibraries,
            parse::parse_file,
            types::{annotated_scheme, def_signature_status, mapped_def_types},
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), std::collections::HashMap::new());
    }

    #[test]
    fn mapped_def_types_maps_function_with_type_params() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with type parameter in signature
        FileSource::new(
            &db,
            file_id,
            r#"fn identity(x: 'a) -> 'a { x }"#.to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let identity_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "identity")
            .expect("should find identity function");

        let mapped = mapped_def_types(&db, identity_def.def_id);

        // The var_map should have exactly one mapping for 'a
        assert_eq!(
            mapped.var_map.len(),
            1,
            "Should have exactly one type variable mapping for 'a"
        );
        // Reverse map should also have one entry
        assert_eq!(
            mapped.reverse_map.len(),
            1,
            "Should have exactly one reverse mapping"
        );
    }

    #[test]
    fn mapped_def_types_returns_empty_for_unannotated_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function without type annotations
        FileSource::new(&db, file_id, r#"fn foo() { 42 }"#.to_string());

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo function");

        let mapped = mapped_def_types(&db, foo_def.def_id);

        // No type variables to map
        assert!(mapped.var_map.is_empty());
        assert!(mapped.reverse_map.is_empty());
    }

    #[test]
    fn mapped_def_types_has_no_mappings_for_concrete_types() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with concrete type annotations (no type variables)
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

        let mapped = mapped_def_types(&db, add_def.def_id);

        // No type variables to map (only concrete types like int)
        assert!(
            mapped.var_map.is_empty(),
            "Concrete types should have no variable mappings"
        );
        assert!(
            mapped.reverse_map.is_empty(),
            "Concrete types should have no reverse mappings"
        );
    }

    #[test]
    fn mapped_def_types_has_no_mappings_for_concrete_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "struct Point { x: int, y: int }".to_string());

        let parse_result = parse_file(&db, file_id);
        let point_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "Point")
            .expect("should find Point struct");

        let mapped = mapped_def_types(&db, point_def.def_id);

        // No type variables in concrete struct fields
        assert!(mapped.var_map.is_empty());
        assert!(mapped.reverse_map.is_empty());
    }

    #[test]
    fn mapped_def_types_maps_generic_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "struct Box { value: 'a }".to_string());

        let parse_result = parse_file(&db, file_id);
        let box_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "Box")
            .expect("should find Box struct");

        let mapped = mapped_def_types(&db, box_def.def_id);

        // Should have exactly one mapping for 'a
        assert_eq!(
            mapped.var_map.len(),
            1,
            "Should have one type variable mapping"
        );
        assert_eq!(
            mapped.reverse_map.len(),
            1,
            "Should have one reverse mapping"
        );
    }

    #[test]
    fn mapped_def_types_returns_default_for_unknown_def() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "fn foo() {}".to_string());

        // Create a fake DefId that doesn't exist
        let fake_def_id = ray_shared::def::DefId {
            file: file_id,
            index: 999,
        };

        let mapped = mapped_def_types(&db, fake_def_id);

        assert!(mapped.var_map.is_empty());
        assert!(mapped.reverse_map.is_empty());
    }

    // Tests for def_signature_status

    #[test]
    fn def_signature_status_fully_annotated_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with all params and return type annotated
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

        let status = def_signature_status(&db, add_def.def_id);
        assert_eq!(status, SignatureStatus::FullyAnnotated);
    }

    #[test]
    fn def_signature_status_return_elided_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with params annotated but arrow body (return elided)
        FileSource::new(&db, file_id, r#"fn double(x: int) => x * 2"#.to_string());

        let parse_result = parse_file(&db, file_id);
        let double_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "double")
            .expect("should find double function");

        let status = def_signature_status(&db, double_def.def_id);
        assert_eq!(status, SignatureStatus::ReturnElided);
    }

    #[test]
    fn def_signature_status_unannotated_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with no annotations
        FileSource::new(&db, file_id, r#"fn foo(x) { x }"#.to_string());

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo function");

        let status = def_signature_status(&db, foo_def.def_id);
        assert_eq!(status, SignatureStatus::Unannotated);
    }

    #[test]
    fn def_signature_status_struct_is_fully_annotated() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Struct is always considered fully annotated
        FileSource::new(&db, file_id, "struct Point { x: int, y: int }".to_string());

        let parse_result = parse_file(&db, file_id);
        let point_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "Point")
            .expect("should find Point struct");

        let status = def_signature_status(&db, point_def.def_id);
        assert_eq!(status, SignatureStatus::FullyAnnotated);
    }

    // Tests for annotated_scheme

    #[test]
    fn annotated_scheme_returns_scheme_for_fully_annotated_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

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

        let scheme = annotated_scheme(&db, add_def.def_id);
        assert!(
            scheme.is_some(),
            "Should return a scheme for fully annotated function"
        );

        let scheme = scheme.unwrap();
        // Should be a function type: (int, int) -> int
        assert!(
            scheme.vars.is_empty(),
            "Concrete function should have no type vars"
        );
        assert!(
            scheme.qualifiers.is_empty(),
            "Simple function should have no qualifiers"
        );
    }

    #[test]
    fn annotated_scheme_returns_none_for_unannotated_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, r#"fn foo(x) { x }"#.to_string());

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo function");

        let scheme = annotated_scheme(&db, foo_def.def_id);
        assert!(
            scheme.is_none(),
            "Should return None for unannotated function"
        );
    }

    #[test]
    fn annotated_scheme_returns_scheme_with_type_vars() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Generic function
        FileSource::new(
            &db,
            file_id,
            r#"fn identity(x: 'a) -> 'a { x }"#.to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let identity_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "identity")
            .expect("should find identity function");

        let scheme = annotated_scheme(&db, identity_def.def_id);
        assert!(
            scheme.is_some(),
            "Should return a scheme for generic function"
        );

        let scheme = scheme.unwrap();
        // Should have one type variable for 'a
        assert_eq!(
            scheme.vars.len(),
            1,
            "Generic function should have one type variable"
        );
    }

    #[test]
    fn annotated_scheme_returns_scheme_for_return_elided_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Arrow body function with elided return type
        FileSource::new(&db, file_id, r#"fn double(x: int) => x * 2"#.to_string());

        let parse_result = parse_file(&db, file_id);
        let double_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "double")
            .expect("should find double function");

        let scheme = annotated_scheme(&db, double_def.def_id);
        assert!(
            scheme.is_some(),
            "Should return a scheme for return-elided function"
        );
    }
}

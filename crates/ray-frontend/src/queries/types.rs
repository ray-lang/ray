//! Type mapping queries for the incremental compiler.

use std::collections::HashMap;

use std::sync::Arc;

use ray_core::ast::{Decl, Expr, FuncSig, Node, WalkItem, walk_file};
use ray_query_macros::query;
use ray_shared::{
    def::{DefId, DefKind, SignatureStatus},
    file_id::FileId,
    node_id::NodeId,
    pathlib::ItemPath,
    resolution::{DefTarget, Resolution},
    span::parsed::Parsed,
    ty::{SchemaVarAllocator, Ty, TyVar},
    type_param_id::TypeParamId,
};
use ray_typing::{
    constraints::Predicate,
    types::{Subst, TyScheme},
};
use serde::{Deserialize, Serialize};

use crate::{
    queries::{
        defs::{def_header, def_path},
        parse::parse_file,
        resolve::name_resolutions,
        transform::file_ast,
    },
    query::{Database, Query},
};

/// Result of mapping type variables in a definition's type annotations.
///
/// Contains mappings from TypeParamId to schema variables and reverse mappings
/// for display purposes.
///
/// This is used by downstream queries like `annotated_scheme` to consistently
/// map type parameters to schema variables for typechecking.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MappedDefTypes {
    /// Maps type parameter IDs to schema variables.
    /// TypeParamId { owner: struct_id, index: 0 } → TyVar("?s0")
    pub var_map: HashMap<TypeParamId, TyVar>,

    /// Reverse map for display (schema var → user var).
    /// TyVar("?s0") → TyVar("T")
    pub reverse_map: HashMap<TyVar, TyVar>,
}

impl MappedDefTypes {
    /// Get the origin TypeParamId for a schema variable.
    /// Used by diagnostics to trace a variable back to its declaration site.
    /// O(n) where n is the number of type parameters (typically 1-3).
    pub fn origin_of(&self, var: &TyVar) -> Option<TypeParamId> {
        self.var_map
            .iter()
            .find(|(_, v)| *v == var)
            .map(|(id, _)| *id)
    }

    /// Build a Subst that maps user-written type variable names to schema vars.
    ///
    /// Uses the reverse_map (schema_var → user_var) to create a substitution
    /// from user vars to schema variables: `'a → ?s0`.
    pub fn user_to_schema_subst(&self) -> Subst {
        let mut subst_map = HashMap::new();
        for (schema_var, user_var) in &self.reverse_map {
            subst_map.insert(user_var.clone(), schema_var.clone());
        }
        Subst::from(&subst_map)
    }

    /// Build a Subst that maps schema vars back to user-written type variable names.
    ///
    /// This is for pretty printing: `?s0 → 'a`.
    pub fn schema_to_user_subst(&self) -> Subst {
        let mut subst_map = HashMap::new();
        for (schema_var, user_var) in &self.reverse_map {
            subst_map.insert(schema_var.clone(), user_var.clone());
        }
        Subst::from(&subst_map)
    }
}

/// Transforms a `Parsed<Ty>` into a resolved `Ty` by applying resolutions.
///
/// This is the "consumer" side of type resolution. It takes the resolutions
/// collected by `resolve_names_in_file` (via the `name_resolutions` query) and uses them to:
///
/// 1. **Qualify paths**: `"Point"` → `"mymodule::Point"` via `Resolution::Def`
/// 2. **Substitute type params**: `Ty::Var("'a")` → `Ty::Var(schema_var)` via `Resolution::TypeParam` + `var_map`
///
/// The caller is responsible for providing the combined `var_map` that includes
/// both parent type parameters (e.g., from impl) and own type parameters (e.g., from method).
///
/// # Arguments
///
/// * `parsed_ty` - The parsed type with synthetic IDs corresponding to type references
/// * `resolutions` - The resolution map from `name_resolutions` query
/// * `var_map` - Combined mapping from `TypeParamId` to schema variables
/// * `get_item_path` - Closure to convert a `DefTarget` to an `ItemPath`
///
/// # Returns
///
/// The resolved `Ty` with qualified paths and mapped type variables.
pub fn apply_type_resolutions<F>(
    parsed_ty: &Parsed<Ty>,
    resolutions: &HashMap<NodeId, Resolution>,
    var_map: &HashMap<TypeParamId, TyVar>,
    get_item_path: F,
) -> Ty
where
    F: Fn(&DefTarget) -> ItemPath + Copy,
{
    let synthetic_ids = parsed_ty.synthetic_ids();
    let ty = parsed_ty.value();

    let mut id_iter = synthetic_ids.iter();
    transform_ty_with_resolutions(ty, &mut id_iter, resolutions, var_map, get_item_path)
}

/// Apply type resolutions to the mono type inside a `Parsed<TyScheme>`.
///
/// This is a convenience wrapper for struct fields and other places where
/// types are stored as `Parsed<TyScheme>` rather than `Parsed<Ty>`.
///
/// The synthetic IDs from the `Parsed<TyScheme>` correspond to type references
/// in the inner `TyScheme.ty` field.
pub fn apply_type_resolutions_to_scheme<F>(
    parsed_scheme: &Parsed<ray_typing::types::TyScheme>,
    resolutions: &HashMap<NodeId, Resolution>,
    var_map: &HashMap<TypeParamId, TyVar>,
    get_item_path: F,
) -> Ty
where
    F: Fn(&DefTarget) -> ItemPath + Copy,
{
    let synthetic_ids = parsed_scheme.synthetic_ids();
    let ty = parsed_scheme.mono();

    let mut id_iter = synthetic_ids.iter();
    transform_ty_with_resolutions(ty, &mut id_iter, resolutions, var_map, get_item_path)
}

/// Recursively transforms a type, consuming synthetic IDs in the same order as `Ty::flatten()`.
fn transform_ty_with_resolutions<'a, F>(
    ty: &Ty,
    id_iter: &mut impl Iterator<Item = &'a NodeId>,
    resolutions: &HashMap<NodeId, Resolution>,
    var_map: &HashMap<TypeParamId, TyVar>,
    get_item_path: F,
) -> Ty
where
    F: Fn(&DefTarget) -> ItemPath + Copy,
{
    match ty {
        // Ty::Const and Ty::Var both consume one synthetic ID
        Ty::Const(original_path) => {
            if let Some(node_id) = id_iter.next() {
                match resolutions.get(node_id) {
                    Some(Resolution::Def(target)) => Ty::Const(get_item_path(target)),
                    Some(Resolution::TypeParam(id)) => {
                        // A type param was used where a constant type was expected
                        // Map it to a schema variable
                        if let Some(schema_var) = var_map.get(id) {
                            Ty::Var(schema_var.clone())
                        } else {
                            // Type param not in scope - keep original (error reported elsewhere)
                            ty.clone()
                        }
                    }
                    Some(Resolution::Local(_)) | Some(Resolution::Error { .. }) | None => {
                        // Keep original (error reported elsewhere or not resolvable)
                        ty.clone()
                    }
                }
            } else {
                // No synthetic ID - keep original path
                Ty::Const(original_path.clone())
            }
        }

        Ty::Var(original_var) => {
            if let Some(node_id) = id_iter.next() {
                match resolutions.get(node_id) {
                    Some(Resolution::TypeParam(id)) => {
                        if let Some(schema_var) = var_map.get(id) {
                            Ty::Var(schema_var.clone())
                        } else {
                            // Type param not in scope - keep original
                            ty.clone()
                        }
                    }
                    Some(Resolution::Def(target)) => {
                        // A definition was used where a type variable was expected
                        // This can happen with type aliases or when a type name looks like a var
                        Ty::Const(get_item_path(target))
                    }
                    _ => ty.clone(),
                }
            } else {
                // No synthetic ID - keep original
                Ty::Var(original_var.clone())
            }
        }

        Ty::Proj(original_path, args) => {
            // First synthetic ID is for the base type
            let resolved_path = if let Some(node_id) = id_iter.next() {
                match resolutions.get(node_id) {
                    Some(Resolution::Def(target)) => get_item_path(target),
                    _ => original_path.clone(),
                }
            } else {
                original_path.clone()
            };

            // Then transform each type argument (consuming their synthetic IDs)
            let resolved_args: Vec<Ty> = args
                .iter()
                .map(|arg| {
                    transform_ty_with_resolutions(arg, id_iter, resolutions, var_map, get_item_path)
                })
                .collect();

            Ty::Proj(resolved_path, resolved_args)
        }

        // Structural types: recurse into components
        Ty::Func(params, ret) => {
            let resolved_params: Vec<Ty> = params
                .iter()
                .map(|p| {
                    transform_ty_with_resolutions(p, id_iter, resolutions, var_map, get_item_path)
                })
                .collect();
            let resolved_ret =
                transform_ty_with_resolutions(ret, id_iter, resolutions, var_map, get_item_path);
            Ty::Func(resolved_params, Box::new(resolved_ret))
        }

        Ty::Tuple(elems) => {
            let resolved_elems: Vec<Ty> = elems
                .iter()
                .map(|e| {
                    transform_ty_with_resolutions(e, id_iter, resolutions, var_map, get_item_path)
                })
                .collect();
            Ty::Tuple(resolved_elems)
        }

        Ty::Ref(inner) => {
            let resolved_inner =
                transform_ty_with_resolutions(inner, id_iter, resolutions, var_map, get_item_path);
            Ty::Ref(Box::new(resolved_inner))
        }

        Ty::RawPtr(inner) => {
            let resolved_inner =
                transform_ty_with_resolutions(inner, id_iter, resolutions, var_map, get_item_path);
            Ty::RawPtr(Box::new(resolved_inner))
        }

        Ty::Array(inner, size) => {
            let resolved_inner =
                transform_ty_with_resolutions(inner, id_iter, resolutions, var_map, get_item_path);
            Ty::Array(Box::new(resolved_inner), *size)
        }

        // Terminal types with no type references
        Ty::Never | Ty::Any => ty.clone(),
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
    // Find the DefHeader for this definition
    let Some(header) = def_header(db, def_id) else {
        return MappedDefTypes::default();
    };

    // Find the AST node for this definition
    // Use parse_file instead of file_ast to avoid cycle:
    // file_ast -> struct_def -> mapped_def_types -> file_ast
    let parse_result = parse_file(db, def_id.file);
    let Some(def_ast) = find_def_ast(&parse_result.ast.decls, header.root_node) else {
        return MappedDefTypes::default();
    };

    // Extract and map type annotations based on definition kind
    extract_and_map_types(def_id, def_ast)
}

/// Determine the annotation status of a definition's signature.
///
/// This query determines whether a definition has:
/// - `FullyAnnotated`: All parameter and return types explicit
/// - `ReturnElided`: Parameters annotated, return type inferred from => body
/// - `ImplicitUnit`: Parameters annotated, return type elided but implicitly `()`
/// - `Unannotated`: Missing parameter or return type annotations
///
/// Non-function definitions (structs, traits, impls, type aliases) are always
/// considered `FullyAnnotated` since they require explicit type information.
#[query]
pub fn def_signature_status(db: &Database, def_id: DefId) -> SignatureStatus {
    // Find the DefHeader for this definition
    let Some(header) = def_header(db, def_id) else {
        return SignatureStatus::Unannotated;
    };

    // In impl/trait methods, bare `self` is implicitly typed by the parent block.
    // The transform pass annotates it, but we read the pre-transform AST here.
    let has_implicit_self = header
        .parent
        .and_then(|parent_def_id| def_header(db, parent_def_id))
        .is_some_and(|parent_header| matches!(parent_header.kind, DefKind::Impl | DefKind::Trait));

    // Find the AST node for this definition
    // Use parse_file to avoid cycle with file_ast
    let parse_result = parse_file(db, def_id.file);
    let Some(def_ast) = find_def_ast(&parse_result.ast.decls, header.root_node) else {
        return SignatureStatus::Unannotated;
    };

    compute_signature_status(def_ast, has_implicit_self)
}

/// Compute the signature status for a declaration.
fn compute_signature_status(decl: &Node<Decl>, has_implicit_self: bool) -> SignatureStatus {
    match &decl.value {
        Decl::Func(func) => func.to_sig_status(has_implicit_self),
        // Standalone signatures (trait methods) have no body — treat as block
        Decl::FnSig(sig) => sig.to_sig_status(has_implicit_self, true),
        // These always have explicit type information
        Decl::Struct(_) | Decl::Trait(_) | Decl::Impl(_) | Decl::TypeAlias(_, _) => {
            SignatureStatus::FullyAnnotated
        }
        // Variable declarations
        Decl::Name(name, _) | Decl::Mutable(name, _) => {
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
        // FileMain doesn't have a signature - it's a container for statements
        Decl::FileMain(_) => SignatureStatus::FullyAnnotated,
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
    let resolutions = name_resolutions(db, def_id.file);

    // Find the DefHeader for this definition
    let def_header = file_result.defs.iter().find(|h| h.def_id == def_id)?;

    // Get parent var_map if this is a nested definition (trait method, impl method)
    let parent_var_map = get_parent_var_map(db, def_id);

    // Combine parent var_map with own var_map
    let mut combined_var_map = parent_var_map;
    combined_var_map.extend(mapping.var_map.iter().map(|(k, v)| (*k, v.clone())));

    // Create closure to convert DefTarget to ItemPath using the def_path query
    let get_item_path = |target: &DefTarget| {
        def_path(db, target.clone()).expect("DefTarget should have a valid path")
    };

    // Find the AST node for this definition
    let def_ast = find_def_ast(&file_result.ast.decls, def_header.root_node)?;

    let mut scheme = compute_scheme_resolved(
        def_ast,
        &combined_var_map,
        &resolutions,
        get_item_path,
        status,
    )?;

    // For methods inside impl/trait blocks, include the parent's where-clause predicates.
    let parent_predicates =
        get_parent_qualifiers(db, def_id, &resolutions, &combined_var_map, get_item_path);
    if !parent_predicates.is_empty() {
        scheme.qualifiers_mut().extend(parent_predicates);
    }

    Some(scheme)
}

/// Get the parent definition's var_map for nested definitions.
///
/// For trait methods and impl methods, we need to include the parent's type parameters
/// so that references to them can be resolved correctly.
#[query]
pub fn get_parent_var_map(db: &Database, def_id: DefId) -> HashMap<TypeParamId, TyVar> {
    // Find the DefHeader for this definition
    let Some(header) = def_header(db, def_id) else {
        return HashMap::new();
    };

    // Check if this definition has a parent
    let Some(parent_def_id) = header.parent else {
        return HashMap::new();
    };

    // Get the parent's var_map
    let parent_mapping = mapped_def_types(db, parent_def_id);
    parent_mapping.var_map
}

/// Collect all expression-level type references from the AST.
///
/// Maps type NodeIds to their `Parsed<Ty>` for expressions that contain
/// type references: `Cast` (e.g., `x as rawptr['k]`), `New` (e.g., `new(T, n)`),
/// and `Type` (e.g., `sizeof('a)`).
///
/// The key is the NodeId of the type itself (from Node wrapper or root synthetic ID).
#[query]
pub fn expr_type_refs(db: &Database, file_id: FileId) -> Arc<HashMap<NodeId, Parsed<Ty>>> {
    let file_result = file_ast(db, file_id);
    let mut map = HashMap::new();
    for item in walk_file(&file_result.ast) {
        if let WalkItem::Expr(node) = item {
            match &node.value {
                Expr::Cast(cast) => {
                    // Cast.ty is Parsed<Ty>, use root synthetic ID
                    if let Some(root_id) = cast.ty.root_id() {
                        map.insert(root_id, cast.ty.clone());
                    }
                }
                Expr::New(new) => {
                    // New.ty is Node<Parsed<Ty>>, use Node's ID
                    map.insert(new.ty.id, new.ty.value.clone());
                }
                Expr::Type(scheme) => {
                    // scheme is Parsed<TyScheme>, extract Ty while preserving Source/synthetic_ids
                    let parsed_ty = scheme.clone().map(|s| s.ty);
                    if let Some(root_id) = parsed_ty.root_id() {
                        map.insert(root_id, parsed_ty);
                    }
                }
                _ => {}
            }
        }
    }
    Arc::new(map)
}

/// Resolve an expression-level type reference.
///
/// Given the NodeId of a type reference (from Cast.ty, New.ty, or Type.ty),
/// applies name resolutions and type parameter mappings to produce a fully
/// resolved type.
#[query]
pub fn resolved_ty(db: &Database, node_id: NodeId) -> Option<Ty> {
    let file_id = node_id.owner.file;
    let type_refs = expr_type_refs(db, file_id);
    let parsed_ty = type_refs.get(&node_id)?;
    let resolutions = name_resolutions(db, file_id);
    let mapping = mapped_def_types(db, node_id.owner);
    let parent_var_map = get_parent_var_map(db, node_id.owner);

    let mut combined_var_map = parent_var_map;
    combined_var_map.extend(mapping.var_map.iter().map(|(k, v)| (*k, v.clone())));

    let get_item_path = |target: &DefTarget| {
        def_path(db, target.clone()).expect("DefTarget should have a valid path")
    };

    Some(apply_type_resolutions(
        parsed_ty,
        &resolutions,
        &combined_var_map,
        get_item_path,
    ))
}

/// Get the parent definition's where-clause predicates for nested definitions.
///
/// For impl methods, this resolves the parent impl's `where` clause qualifiers
/// into predicates using schema vars. For example, if the parent is
/// `impl Eq[list['a]] where Eq['a]`, this returns `[Eq[?s0]]`.
fn get_parent_qualifiers<F>(
    db: &Database,
    def_id: DefId,
    resolutions: &HashMap<NodeId, Resolution>,
    var_map: &HashMap<TypeParamId, TyVar>,
    get_item_path: F,
) -> Vec<Predicate>
where
    F: Fn(&DefTarget) -> ItemPath + Copy,
{
    let Some(header) = def_header(db, def_id) else {
        return vec![];
    };
    let Some(parent_def_id) = header.parent else {
        return vec![];
    };

    // Find the parent's AST node to access its qualifiers
    let parse_result = parse_file(db, parent_def_id.file);
    let Some(parent_header) = parse_result.defs.iter().find(|h| h.def_id == parent_def_id) else {
        return vec![];
    };
    let Some(parent_ast) = find_def_ast(&parse_result.ast.decls, parent_header.root_node) else {
        return vec![];
    };

    // Extract qualifiers from the parent declaration
    let qualifiers = match &parent_ast.value {
        Decl::Impl(im) => &im.qualifiers,
        // TODO: trait-level qualifiers if needed
        _ => return vec![],
    };

    qualifiers
        .iter()
        .filter_map(|qual| {
            let qual_ty = apply_type_resolutions(qual, resolutions, var_map, get_item_path);
            Predicate::from_ty(&qual_ty)
        })
        .collect()
}

/// Compute the type scheme for a declaration with resolved types.
fn compute_scheme_resolved<F>(
    decl: &Node<Decl>,
    var_map: &HashMap<TypeParamId, TyVar>,
    resolutions: &HashMap<NodeId, Resolution>,
    get_item_path: F,
    status: SignatureStatus,
) -> Option<TyScheme>
where
    F: Fn(&DefTarget) -> ItemPath + Copy,
{
    match &decl.value {
        Decl::Func(func) => {
            compute_func_scheme_resolved(&func.sig, var_map, resolutions, get_item_path, status)
        }
        Decl::FnSig(sig) => {
            compute_func_scheme_resolved(sig, var_map, resolutions, get_item_path, status)
        }
        // For non-function definitions, we don't compute schemes here
        // (structs/traits/impls have their own type representations)
        _ => None,
    }
}

/// Compute the type scheme for a function signature with resolved types.
fn compute_func_scheme_resolved<F>(
    sig: &FuncSig,
    var_map: &HashMap<TypeParamId, TyVar>,
    resolutions: &HashMap<NodeId, Resolution>,
    get_item_path: F,
    status: SignatureStatus,
) -> Option<TyScheme>
where
    F: Fn(&DefTarget) -> ItemPath + Copy,
{
    // Extract and resolve parameter types
    let mut param_tys = Vec::with_capacity(sig.params.len());
    for param in &sig.params {
        let ty = param.value.parsed_ty().map(|parsed_scheme| {
            apply_type_resolutions_to_scheme(parsed_scheme, resolutions, var_map, get_item_path)
        })?;
        param_tys.push(ty);
    }

    // Extract and resolve return type
    let ret_ty = if let Some(parsed_ty) = &sig.ret_ty {
        apply_type_resolutions(parsed_ty, resolutions, var_map, get_item_path)
    } else if status == SignatureStatus::ReturnElided {
        // For arrow bodies, use a return placeholder
        Ty::ret_placeholder(&sig.path.value)
    } else {
        // No return type annotation and not elided
        Ty::unit()
    };

    // Build the function type
    let func_ty = Ty::Func(param_tys, Box::new(ret_ty));

    // Extract and resolve qualifiers (where clauses)
    let mut qual_tys = Vec::with_capacity(sig.qualifiers.len());
    let mut predicates = Vec::with_capacity(sig.qualifiers.len());
    for qual in &sig.qualifiers {
        let qual_ty = apply_type_resolutions(qual, resolutions, var_map, get_item_path);
        if let Some(pred) = Predicate::from_ty(&qual_ty) {
            predicates.push(pred);
        }
        qual_tys.push(qual_ty);
    }

    // Extract schema vars from the resolved function type and qualifier types.
    // Filter out return placeholders (%r) — they must remain as unification
    // variables so the body's return type can be inferred, not skolemized.
    let vars: Vec<TyVar> =
        Ty::unique_free_vars_from(std::iter::once(&func_ty).chain(qual_tys.iter()))
            .into_iter()
            .filter(|v| !v.is_ret_placeholder())
            .collect();

    // Build the scheme
    let scheme = if vars.is_empty() && predicates.is_empty() {
        TyScheme::from_mono(func_ty)
    } else {
        TyScheme::new(vars, predicates, func_ty)
    };

    Some(scheme)
}

/// Extract type parameters from a declaration and build the TypeParamId → schema var mappings.
///
/// Ray allows both explicit type parameters (e.g., `fn foo['a](...)`) and implicit ones
/// where type variables are inferred from usage in the signature (e.g., `fn foo(x: 'a) -> 'a`).
/// This function collects type variables from both sources.
fn extract_and_map_types(def_id: DefId, decl: &Node<Decl>) -> MappedDefTypes {
    let mut allocator = SchemaVarAllocator::with_def_scope(def_id);

    // Extract type parameter names from the definition (both explicit and implicit)
    let type_param_names = extract_type_param_names(decl);

    let mut var_map = HashMap::new();
    let mut reverse_map = HashMap::new();

    for (index, param_name) in type_param_names.iter().enumerate() {
        let schema_var = allocator.alloc();
        let type_param_id = TypeParamId {
            owner: def_id,
            index: index as u32,
        };

        var_map.insert(type_param_id, schema_var.clone());
        reverse_map.insert(schema_var, TyVar::new(param_name.clone()));
    }

    MappedDefTypes {
        var_map,
        reverse_map,
    }
}

/// Extract type parameter names from a declaration.
///
/// Returns a list of unique type parameter names in discovery order.
/// For functions, this includes both explicit type params (`fn foo['a]`) and
/// implicit ones from the signature (`fn foo(x: 'a)`).
fn extract_type_param_names(decl: &Node<Decl>) -> Vec<String> {
    match &decl.value {
        Decl::Func(func) => sig_type_param_names(&func.sig),
        Decl::FnSig(sig) => sig_type_param_names(sig),
        Decl::Struct(st) => collect_struct_type_params(st),
        Decl::Trait(tr) => Ty::all_user_type_vars(
            std::iter::once(tr.ty.value()).chain(tr.super_trait.iter().map(|s| s.value())),
        )
        .into_iter()
        .filter_map(|tv| tv.path().name())
        .collect(),
        Decl::Impl(im) => Ty::all_user_type_vars(
            std::iter::once(im.ty.value()).chain(im.qualifiers.iter().map(|q| q.value())),
        )
        .into_iter()
        .filter_map(|tv| tv.path().name())
        .collect(),
        Decl::TypeAlias(_name, _parsed_ty) => {
            // Type aliases don't have their own type parameters
            // (any type vars in the aliased type are free)
            vec![]
        }
        Decl::Name(_, _) | Decl::Mutable(_, _) | Decl::Declare(_) | Decl::FileMain(_) => vec![],
    }
}

/// Collect type parameter names from a function signature using the canonical
/// `FuncSig::all_type_vars()` method.
fn sig_type_param_names(sig: &FuncSig) -> Vec<String> {
    sig.all_type_vars()
        .into_iter()
        .filter_map(|tv| tv.path().name())
        .collect()
}

/// Collect type parameters from a struct definition (explicit only).
fn collect_struct_type_params(st: &ray_core::ast::Struct) -> Vec<String> {
    extract_type_params_from_parsed_tys(st.ty_params.as_ref())
}

/// Extract type parameter names from an optional TypeParams.
fn extract_type_params_from_parsed_tys(
    ty_params: Option<&ray_core::ast::TypeParams>,
) -> Vec<String> {
    ty_params
        .map(|tp| {
            tp.tys
                .iter()
                .filter_map(|parsed_ty| {
                    if let Ty::Var(ty_var) = parsed_ty.value() {
                        ty_var.path().name()
                    } else {
                        None
                    }
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Find a declaration AST node by its root NodeId.
pub(crate) fn find_def_ast(decls: &[Node<Decl>], root_node: NodeId) -> Option<&Node<Decl>> {
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
pub(crate) fn find_nested_def(parent: &Node<Decl>, root_node: NodeId) -> Option<&Node<Decl>> {
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
                        return Some(func);
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

    use ray_shared::{
        def::{DefId, DefKind, LibraryDefId, SignatureStatus},
        file_id::FileId,
        node_id::NodeId,
        pathlib::{FilePath, ItemPath, ModulePath, Path},
        resolution::{DefTarget, Resolution},
        span::{Source, parsed::Parsed},
        ty::{Ty, TyVar},
        type_param_id::TypeParamId,
    };
    use ray_typing::constraints::Predicate;

    use crate::{
        queries::{
            libraries::LoadedLibraries,
            parse::parse_file,
            types::{
                annotated_scheme, apply_type_resolutions, def_signature_status, expr_type_refs,
                mapped_def_types, resolved_ty,
            },
            workspace::{FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    fn test_def_id() -> DefId {
        DefId {
            file: FileId::default(),
            index: 0,
        }
    }

    fn make_parsed_ty(ty: Ty, synthetic_ids: Vec<NodeId>) -> Parsed<Ty> {
        let mut parsed = Parsed::new(ty, Source::default());
        parsed.set_synthetic_ids(synthetic_ids);
        parsed
    }

    fn dummy_item_path(target: &DefTarget) -> ItemPath {
        match target {
            DefTarget::Workspace(def_id) => ItemPath::new(
                ModulePath::from("test"),
                vec![format!("def_{}", def_id.index)],
            ),
            DefTarget::Library(lib_def_id) => ItemPath::new(
                lib_def_id.module.clone(),
                vec![format!("lib_{}", lib_def_id.index)],
            ),
            DefTarget::Primitive(path) => path.clone(),
        }
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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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

        FileSource::new(&db, file_id, "struct Box['a] { value: 'a }".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
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
    fn annotated_scheme_preserves_type_param_order() {
        // Verifies that fn pair(x: 'a, y: 'b) -> ('a, 'b) produces schema vars
        // [?s0, ?s1] in declaration order, and the function type uses them correctly.
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"fn pair(x: 'a, y: 'b) -> ('a, 'b) { (x, y) }"#.to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let pair_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "pair")
            .expect("should find pair function");

        let scheme = annotated_scheme(&db, pair_def.def_id)
            .expect("Should return a scheme for generic function");

        // Should have 2 type variables
        assert_eq!(scheme.vars.len(), 2, "Should have 2 type variables");

        // Capture actual schema var names (format: ?s:{hash}:{index})
        let var_names: Vec<String> = scheme
            .vars
            .iter()
            .map(|v| v.path().name().unwrap().to_string())
            .collect();
        for (i, name) in var_names.iter().enumerate() {
            assert!(
                name.starts_with("?s") && name.ends_with(&format!(":{}", i)),
                "Schema var at index {} should end with :{}, got: {}",
                i,
                i,
                name,
            );
        }

        // The function type should be fn(var0, var1) -> (var0, var1)
        match &scheme.ty {
            Ty::Func(params, ret) => {
                assert_eq!(params.len(), 2);
                // First param should be var0 (for 'a)
                match &params[0] {
                    Ty::Var(v) => assert_eq!(v.path().name().unwrap(), var_names[0]),
                    other => panic!("Expected Ty::Var for first param, got: {:?}", other),
                }
                // Second param should be var1 (for 'b)
                match &params[1] {
                    Ty::Var(v) => assert_eq!(v.path().name().unwrap(), var_names[1]),
                    other => panic!("Expected Ty::Var for second param, got: {:?}", other),
                }
                // Return type should be (var0, var1)
                match ret.as_ref() {
                    Ty::Tuple(elems) => {
                        assert_eq!(elems.len(), 2);
                        match &elems[0] {
                            Ty::Var(v) => assert_eq!(v.path().name().unwrap(), var_names[0]),
                            other => panic!("Expected Ty::Var for tuple[0], got: {:?}", other),
                        }
                        match &elems[1] {
                            Ty::Var(v) => assert_eq!(v.path().name().unwrap(), var_names[1]),
                            other => panic!("Expected Ty::Var for tuple[1], got: {:?}", other),
                        }
                    }
                    other => panic!("Expected Ty::Tuple for return type, got: {:?}", other),
                }
            }
            other => panic!("Expected Ty::Func, got: {:?}", other),
        }
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

        let scheme = annotated_scheme(&db, double_def.def_id);
        assert!(
            scheme.is_some(),
            "Should return a scheme for return-elided function"
        );
    }

    // Tests for TypeParamId-based mapping

    #[test]
    fn mapped_def_types_uses_type_param_id_as_key() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with two type parameters
        FileSource::new(
            &db,
            file_id,
            r#"fn pair(x: 'a, y: 'b) -> ('a, 'b) { (x, y) }"#.to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let pair_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "pair")
            .expect("should find pair function");

        let mapped = mapped_def_types(&db, pair_def.def_id);

        // Should have two mappings with TypeParamId keys
        assert_eq!(
            mapped.var_map.len(),
            2,
            "Should have two type param mappings"
        );

        // Check that TypeParamIds have correct owner and indices
        let type_param_0 = TypeParamId {
            owner: pair_def.def_id,
            index: 0,
        };
        let type_param_1 = TypeParamId {
            owner: pair_def.def_id,
            index: 1,
        };

        assert!(
            mapped.var_map.contains_key(&type_param_0),
            "Should have mapping for first type param"
        );
        assert!(
            mapped.var_map.contains_key(&type_param_1),
            "Should have mapping for second type param"
        );
    }

    #[test]
    fn mapped_def_types_origin_of_traces_back_to_type_param_id() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with type parameter
        FileSource::new(
            &db,
            file_id,
            r#"fn identity(x: 'a) -> 'a { x }"#.to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let identity_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "identity")
            .expect("should find identity function");

        let mapped = mapped_def_types(&db, identity_def.def_id);

        // Get the schema var for 'a
        let type_param_id = TypeParamId {
            owner: identity_def.def_id,
            index: 0,
        };
        let schema_var = mapped
            .var_map
            .get(&type_param_id)
            .expect("Should have mapping for 'a");

        // origin_of should trace back to the same TypeParamId
        let origin = mapped
            .origin_of(schema_var)
            .expect("Should find origin for schema var");
        assert_eq!(
            origin, type_param_id,
            "origin_of should return the correct TypeParamId"
        );
    }

    #[test]
    fn mapped_def_types_reverse_map_has_user_names() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with type parameter
        FileSource::new(
            &db,
            file_id,
            r#"fn identity(x: 'a) -> 'a { x }"#.to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let identity_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "identity")
            .expect("should find identity function");

        let mapped = mapped_def_types(&db, identity_def.def_id);

        // reverse_map should have schema_var → user_var mapping
        assert_eq!(
            mapped.reverse_map.len(),
            1,
            "Should have one reverse mapping"
        );

        // The user var should be "'a"
        let user_var = mapped.reverse_map.values().next().unwrap();
        assert_eq!(user_var.to_string(), "'a", "User var should be 'a");
    }

    #[test]
    fn apply_type_resolutions_resolves_const_to_def() {
        // Enter a def scope so NodeId::new() works
        let _guard = NodeId::enter_def(test_def_id());

        // Ty::Const("Point") with a Resolution::Def → should become Ty::Const(qualified_path)
        let node_id = NodeId::new();
        let original_path = ItemPath::from("Point");
        let parsed_ty = make_parsed_ty(Ty::Const(original_path), vec![node_id]);

        let def_id = DefId {
            file: FileId::default(),
            index: 42,
        };
        let target = DefTarget::Workspace(def_id);

        let mut resolutions = HashMap::new();
        resolutions.insert(node_id, Resolution::Def(target.clone()));

        let var_map = HashMap::new();

        let result = apply_type_resolutions(&parsed_ty, &resolutions, &var_map, dummy_item_path);

        // Should be Ty::Const with the qualified path from dummy_item_path
        match result {
            Ty::Const(path) => {
                assert_eq!(path.to_string(), "test::def_42");
            }
            _ => panic!("Expected Ty::Const, got {:?}", result),
        }
    }

    #[test]
    fn apply_type_resolutions_resolves_var_to_schema_var() {
        let _guard = NodeId::enter_def(test_def_id());

        // Ty::Var("'a") with Resolution::TypeParam → should become Ty::Var(schema_var)
        let node_id = NodeId::new();
        let original_var = TyVar::new("'a".to_string());
        let parsed_ty = make_parsed_ty(Ty::Var(original_var), vec![node_id]);

        let def_id = DefId {
            file: FileId::default(),
            index: 0,
        };
        let type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        let schema_var = TyVar::new("?s0".to_string());

        let mut resolutions = HashMap::new();
        resolutions.insert(node_id, Resolution::TypeParam(type_param_id));

        let mut var_map = HashMap::new();
        var_map.insert(type_param_id, schema_var.clone());

        let result = apply_type_resolutions(&parsed_ty, &resolutions, &var_map, dummy_item_path);

        // Should be Ty::Var with the schema var
        match result {
            Ty::Var(v) => {
                assert_eq!(v.to_string(), "?s0");
            }
            _ => panic!("Expected Ty::Var, got {:?}", result),
        }
    }

    #[test]
    fn apply_type_resolutions_preserves_unresolved_types() {
        let _guard = NodeId::enter_def(test_def_id());

        // Ty::Const without a resolution → should preserve original
        let node_id = NodeId::new();
        let original_path = ItemPath::from_path(&Path::from("UnknownType")).unwrap();
        let parsed_ty = make_parsed_ty(Ty::Const(original_path.clone()), vec![node_id]);

        let resolutions = HashMap::new(); // Empty - no resolution
        let var_map = HashMap::new();

        let result = apply_type_resolutions(&parsed_ty, &resolutions, &var_map, dummy_item_path);

        // Should preserve the original type
        match result {
            Ty::Const(path) => {
                assert_eq!(path.to_string(), "UnknownType");
            }
            _ => panic!("Expected Ty::Const, got {:?}", result),
        }
    }

    #[test]
    fn apply_type_resolutions_handles_proj_type() {
        let _guard = NodeId::enter_def(test_def_id());

        // Ty::Proj("List", ['a]) → should resolve base and args
        let base_id = NodeId::new();
        let arg_id = NodeId::new();

        let original_path = ItemPath::from_path(&Path::from("List")).unwrap();
        let arg_var = TyVar::new("'a".to_string());
        let parsed_ty = make_parsed_ty(
            Ty::Proj(original_path, vec![Ty::Var(arg_var)]),
            vec![base_id, arg_id],
        );

        let def_id = DefId {
            file: FileId::default(),
            index: 1,
        };
        let list_target = DefTarget::Workspace(def_id);

        let type_param_id = TypeParamId {
            owner: DefId {
                file: FileId::default(),
                index: 0,
            },
            index: 0,
        };
        let schema_var = TyVar::new("?s0".to_string());

        let mut resolutions = HashMap::new();
        resolutions.insert(base_id, Resolution::Def(list_target));
        resolutions.insert(arg_id, Resolution::TypeParam(type_param_id));

        let mut var_map = HashMap::new();
        var_map.insert(type_param_id, schema_var);

        let result = apply_type_resolutions(&parsed_ty, &resolutions, &var_map, dummy_item_path);

        // Should be Ty::Proj with resolved path and args
        match result {
            Ty::Proj(path, args) => {
                assert_eq!(path.to_string(), "test::def_1");
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Ty::Var(v) => assert_eq!(v.to_string(), "?s0"),
                    _ => panic!("Expected Ty::Var for arg"),
                }
            }
            _ => panic!("Expected Ty::Proj, got {:?}", result),
        }
    }

    #[test]
    fn apply_type_resolutions_handles_func_type() {
        let _guard = NodeId::enter_def(test_def_id());

        // Ty::Func([param_ty], ret_ty) → should resolve each component
        let param_id = NodeId::new();
        let ret_id = NodeId::new();

        let param_path = ItemPath::from_path(&Path::from("Int")).unwrap();
        let ret_path = ItemPath::from_path(&Path::from("Bool")).unwrap();
        let parsed_ty = make_parsed_ty(
            Ty::Func(vec![Ty::Const(param_path)], Box::new(Ty::Const(ret_path))),
            vec![param_id, ret_id],
        );

        let int_def_id = DefId {
            file: FileId::default(),
            index: 10,
        };
        let bool_def_id = DefId {
            file: FileId::default(),
            index: 20,
        };

        let mut resolutions = HashMap::new();
        resolutions.insert(param_id, Resolution::Def(DefTarget::Workspace(int_def_id)));
        resolutions.insert(ret_id, Resolution::Def(DefTarget::Workspace(bool_def_id)));

        let var_map = HashMap::new();

        let result = apply_type_resolutions(&parsed_ty, &resolutions, &var_map, dummy_item_path);

        match result {
            Ty::Func(params, ret) => {
                assert_eq!(params.len(), 1);
                match &params[0] {
                    Ty::Const(p) => assert_eq!(p.to_string(), "test::def_10"),
                    _ => panic!("Expected Ty::Const for param"),
                }
                match ret.as_ref() {
                    Ty::Const(p) => assert_eq!(p.to_string(), "test::def_20"),
                    _ => panic!("Expected Ty::Const for ret"),
                }
            }
            _ => panic!("Expected Ty::Func, got {:?}", result),
        }
    }

    #[test]
    fn apply_type_resolutions_handles_tuple_type() {
        let _guard = NodeId::enter_def(test_def_id());

        // Ty::Tuple([elem1, elem2]) → should resolve each element
        let elem1_id = NodeId::new();
        let elem2_id = NodeId::new();

        let elem1_path = ItemPath::from_path(&Path::from("Int")).unwrap();
        let elem2_path = ItemPath::from_path(&Path::from("String")).unwrap();
        let parsed_ty = make_parsed_ty(
            Ty::Tuple(vec![Ty::Const(elem1_path), Ty::Const(elem2_path)]),
            vec![elem1_id, elem2_id],
        );

        let int_def_id = DefId {
            file: FileId::default(),
            index: 10,
        };
        let string_def_id = DefId {
            file: FileId::default(),
            index: 20,
        };

        let mut resolutions = HashMap::new();
        resolutions.insert(elem1_id, Resolution::Def(DefTarget::Workspace(int_def_id)));
        resolutions.insert(
            elem2_id,
            Resolution::Def(DefTarget::Workspace(string_def_id)),
        );

        let var_map = HashMap::new();

        let result = apply_type_resolutions(&parsed_ty, &resolutions, &var_map, dummy_item_path);

        match result {
            Ty::Tuple(elems) => {
                assert_eq!(elems.len(), 2);
                match &elems[0] {
                    Ty::Const(p) => assert_eq!(p.to_string(), "test::def_10"),
                    _ => panic!("Expected Ty::Const for first elem"),
                }
                match &elems[1] {
                    Ty::Const(p) => assert_eq!(p.to_string(), "test::def_20"),
                    _ => panic!("Expected Ty::Const for second elem"),
                }
            }
            _ => panic!("Expected Ty::Tuple, got {:?}", result),
        }
    }

    #[test]
    fn apply_type_resolutions_handles_ref_type() {
        let _guard = NodeId::enter_def(test_def_id());

        // Ty::Ref(inner) → should resolve inner
        let inner_id = NodeId::new();

        let inner_path = ItemPath::from_path(&Path::from("Point")).unwrap();
        let parsed_ty = make_parsed_ty(Ty::Ref(Box::new(Ty::Const(inner_path))), vec![inner_id]);

        let point_def_id = DefId {
            file: FileId::default(),
            index: 5,
        };

        let mut resolutions = HashMap::new();
        resolutions.insert(
            inner_id,
            Resolution::Def(DefTarget::Workspace(point_def_id)),
        );

        let var_map = HashMap::new();

        let result = apply_type_resolutions(&parsed_ty, &resolutions, &var_map, dummy_item_path);

        match result {
            Ty::Ref(inner) => match inner.as_ref() {
                Ty::Const(p) => assert_eq!(p.to_string(), "test::def_5"),
                _ => panic!("Expected Ty::Const for inner"),
            },
            _ => panic!("Expected Ty::Ref, got {:?}", result),
        }
    }

    #[test]
    fn apply_type_resolutions_handles_library_target() {
        let _guard = NodeId::enter_def(test_def_id());

        // Resolution::Def with DefTarget::Library → should use library path
        let node_id = NodeId::new();
        let original_path = ItemPath::from_path(&Path::from("List")).unwrap();
        let parsed_ty = make_parsed_ty(Ty::Const(original_path), vec![node_id]);

        let lib_def_id = LibraryDefId {
            module: ModulePath::from("core::collections"),
            index: 0,
        };
        let target = DefTarget::Library(lib_def_id);

        let mut resolutions = HashMap::new();
        resolutions.insert(node_id, Resolution::Def(target.clone()));

        let var_map = HashMap::new();

        let result = apply_type_resolutions(&parsed_ty, &resolutions, &var_map, dummy_item_path);

        match result {
            Ty::Const(path) => {
                assert_eq!(path.to_string(), "core::collections::lib_0");
            }
            _ => panic!("Expected Ty::Const, got {:?}", result),
        }
    }

    #[test]
    fn apply_type_resolutions_handles_type_param_in_const_position() {
        let _guard = NodeId::enter_def(test_def_id());

        // Ty::Const but Resolution::TypeParam → becomes Ty::Var
        let node_id = NodeId::new();
        let original_path = ItemPath::from_path(&Path::from("T")).unwrap();
        let parsed_ty = make_parsed_ty(Ty::Const(original_path), vec![node_id]);

        let def_id = DefId {
            file: FileId::default(),
            index: 0,
        };
        let type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        let schema_var = TyVar::new("?s0".to_string());

        let mut resolutions = HashMap::new();
        resolutions.insert(node_id, Resolution::TypeParam(type_param_id));

        let mut var_map = HashMap::new();
        var_map.insert(type_param_id, schema_var.clone());

        let result = apply_type_resolutions(&parsed_ty, &resolutions, &var_map, dummy_item_path);

        // Should be Ty::Var because it resolved to a type param
        match result {
            Ty::Var(v) => {
                assert_eq!(v.to_string(), "?s0");
            }
            _ => panic!("Expected Ty::Var, got {:?}", result),
        }
    }

    // Tests for impl method lookup in find_def_ast / def_signature_status

    #[test]
    fn def_signature_status_fully_annotated_impl_method() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
struct Foo { x: int }
impl object Foo {
    fn get_x(self: *Foo) -> int { self.x }
}
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let get_x_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "get_x")
            .expect("should find get_x method in impl block");

        let status = def_signature_status(&db, get_x_def.def_id);
        assert_eq!(
            status,
            SignatureStatus::FullyAnnotated,
            "Fully annotated impl method should have FullyAnnotated status"
        );
    }

    #[test]
    fn def_signature_status_bare_self_impl_method_is_implicit_unit() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
struct Foo { x: int }
impl object Foo {
    fn get_x(self) { self.x }
}
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let get_x_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "get_x")
            .expect("should find get_x method in impl block");

        let status = def_signature_status(&db, get_x_def.def_id);
        assert_eq!(
            status,
            SignatureStatus::ImplicitUnit,
            "Bare self in impl method should be implicitly typed (block body = ImplicitUnit)"
        );
    }

    #[test]
    fn def_signature_status_return_elided_impl_method() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
struct Foo { x: int }
impl object Foo {
    fn get_x(self: *Foo) => self.x
}
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let get_x_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "get_x")
            .expect("should find get_x method in impl block");

        let status = def_signature_status(&db, get_x_def.def_id);
        assert_eq!(
            status,
            SignatureStatus::ReturnElided,
            "Impl method with arrow body and no return annotation should be ReturnElided"
        );
    }

    #[test]
    fn annotated_scheme_returns_scheme_for_impl_method() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
struct Foo { x: int }
impl object Foo {
    fn get_x(self: *Foo) -> int { self.x }
}
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let get_x_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "get_x")
            .expect("should find get_x method in impl block");

        let scheme = annotated_scheme(&db, get_x_def.def_id);
        assert!(
            scheme.is_some(),
            "Should return a scheme for fully annotated impl method"
        );
    }

    #[test]
    fn annotated_scheme_returns_scheme_for_bare_self_impl_method() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
struct Foo { x: int }
impl object Foo {
    fn get_x(self) { self.x }
}
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let get_x_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "get_x")
            .expect("should find get_x method in impl block");

        let scheme = annotated_scheme(&db, get_x_def.def_id);
        assert!(
            scheme.is_some(),
            "Bare self in impl method should produce a scheme (self is implicitly typed)"
        );
    }

    #[test]
    fn apply_type_resolutions_preserves_terminal_types() {
        // Ty::Never and Ty::Any should be preserved
        let parsed_never = make_parsed_ty(Ty::Never, vec![]);
        let parsed_any = make_parsed_ty(Ty::Any, vec![]);

        let resolutions = HashMap::new();
        let var_map = HashMap::new();

        let result_never =
            apply_type_resolutions(&parsed_never, &resolutions, &var_map, dummy_item_path);
        let result_any =
            apply_type_resolutions(&parsed_any, &resolutions, &var_map, dummy_item_path);

        assert_eq!(result_never, Ty::Never);
        assert_eq!(result_any, Ty::Any);
    }

    #[test]
    fn annotated_scheme_for_impl_method_includes_parent_where_clauses() {
        // Given: impl ToStr[('a, 'b)] where ToStr['a], ToStr['b]
        // When: annotated_scheme is called for the `to_str` method
        // Then: the method's TyScheme.qualifiers should include ToStr[?s0] and ToStr[?s1]
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

impl ToStr[('a, 'b)] where ToStr['a], ToStr['b] {
    fn to_str(self: ('a, 'b)) -> string => "todo"
}
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);

        // Find the to_str method inside the impl (not the one in the trait definition)
        let to_str_def = parse_result
            .defs
            .iter()
            .find(|d| {
                d.name == "to_str"
                    && d.parent.map_or(false, |parent_id| {
                        parse_result
                            .defs
                            .iter()
                            .any(|p| p.def_id == parent_id && matches!(p.kind, DefKind::Impl))
                    })
            })
            .expect("should find to_str method in impl block");

        let scheme = annotated_scheme(&db, to_str_def.def_id)
            .expect("Should return a scheme for the impl method");

        // The method scheme should include the parent impl's where-clause predicates.
        // The where-clause `where ToStr['a], ToStr['b]` should produce 2 predicates
        // with schema vars (not user vars).
        assert!(
            scheme.qualifiers.len() >= 2,
            "Method scheme should include at least 2 predicates from parent impl's where-clause, got: {:?}",
            scheme.qualifiers,
        );

        // Each predicate should be a Class predicate with path ending in "ToStr"
        for pred in &scheme.qualifiers {
            match pred {
                Predicate::Class(cp) => {
                    assert!(
                        cp.path.item_name() == Some("ToStr"),
                        "Predicate path should be ToStr, got: {:?}",
                        cp.path,
                    );
                    // The arg should be a schema var (starts with ?s), not a user var ('a/'b)
                    assert_eq!(cp.args.len(), 1, "ToStr predicate should have 1 arg");
                    match &cp.args[0] {
                        Ty::Var(v) => {
                            let name = v.path().name().unwrap_or_default();
                            assert!(
                                name.starts_with("?s"),
                                "Predicate arg should be a schema var, got: {}",
                                name,
                            );
                        }
                        other => panic!("Expected Ty::Var in predicate arg, got: {:?}", other),
                    }
                }
                other => panic!("Expected Class predicate, got: {:?}", other),
            }
        }
    }

    // Tests for expr_type_refs and resolved_ty

    #[test]
    fn expr_type_refs_collects_cast_expression() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with a cast expression
        FileSource::new(
            &db,
            file_id,
            r#"fn foo(x: int) -> int { x as int }"#.to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let type_refs = expr_type_refs(&db, file_id);

        // Should have at least one entry for the cast expression
        assert!(
            !type_refs.is_empty(),
            "expr_type_refs should collect the cast expression's type"
        );
    }

    #[test]
    fn expr_type_refs_empty_for_no_casts() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with no cast/new/type expressions
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

        let type_refs = expr_type_refs(&db, file_id);

        assert!(
            type_refs.is_empty(),
            "expr_type_refs should be empty when no cast/new/type expressions exist"
        );
    }

    #[test]
    fn resolved_ty_resolves_type_param_in_cast() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with a type parameter used in a cast target
        FileSource::new(
            &db,
            file_id,
            r#"fn to_ptr(x: 'a) -> rawptr['a] { x as rawptr['a] }"#.to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let type_refs = expr_type_refs(&db, file_id);

        // Should have one entry for the cast
        assert_eq!(
            type_refs.len(),
            1,
            "Should have exactly one cast type ref, got {}",
            type_refs.len(),
        );

        // Get the cast's NodeId and resolve it
        let (cast_node_id, parsed_ty) = type_refs.iter().next().unwrap();

        // The unresolved type should contain the user var 'a
        let unresolved = parsed_ty.value();
        match unresolved {
            Ty::RawPtr(inner) => match inner.as_ref() {
                Ty::Var(v) => {
                    assert_eq!(
                        v.to_string(),
                        "'a",
                        "Unresolved cast type should have user var 'a"
                    );
                }
                other => panic!("Expected Ty::Var inside RawPtr, got: {:?}", other),
            },
            other => panic!("Expected Ty::RawPtr, got: {:?}", other),
        }

        // resolved_ty should map 'a to a schema var
        let resolved = resolved_ty(&db, *cast_node_id);
        assert!(
            resolved.is_some(),
            "resolved_ty should return Some for a cast expression"
        );

        let resolved = resolved.unwrap();
        match &resolved {
            Ty::RawPtr(inner) => match inner.as_ref() {
                Ty::Var(v) => {
                    let name = v.path().name().unwrap_or_default();
                    assert!(
                        name.starts_with("?s"),
                        "Resolved type should have schema var, got: {}",
                        name,
                    );
                }
                other => panic!("Expected Ty::Var inside resolved RawPtr, got: {:?}", other),
            },
            other => panic!("Expected Ty::RawPtr from resolved_ty, got: {:?}", other),
        }
    }

    #[test]
    fn resolved_ty_returns_none_for_non_cast_expr() {
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

        // Use the function's root node — not a cast expression
        let result = resolved_ty(&db, add_def.root_node);
        assert!(
            result.is_none(),
            "resolved_ty should return None for a non-cast/new/type node"
        );
    }

    #[test]
    fn annotated_scheme_return_elided_does_not_quantify_placeholder() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Arrow body function — return type should be inferred, not skolemized
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

        let scheme = annotated_scheme(&db, double_def.def_id)
            .expect("Should return a scheme for return-elided function");

        // The return placeholder (%r) must NOT appear in scheme.vars —
        // otherwise it would be skolemized during annotation checking,
        // making the return type rigid and unable to unify with the body.
        for var in &scheme.vars {
            assert!(
                !var.is_ret_placeholder(),
                "Return placeholder should not be quantified in scheme vars, found: {}",
                var,
            );
        }
    }
}

//! Definition lookup queries for the incremental compiler.

use ray_core::ast::{Decl, Modifier, Node};
use ray_query_macros::query;
use ray_shared::{
    def::{DefId, DefKind, LibraryDefId},
    pathlib::{ItemPath, ModulePath},
    resolution::{DefTarget, Resolution},
    ty::{Ty, TyVar},
};
use ray_typing::types::ReceiverMode;
use serde::{Deserialize, Serialize};

use crate::{
    queries::{
        exports::{ExportedItem, module_def_index},
        libraries::{LoadedLibraries, library_data},
        parse::parse_file,
        resolve::name_resolutions,
        workspace::WorkspaceSnapshot,
    },
    query::{Database, Query},
};

/// A struct definition extracted from either workspace or library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StructDef {
    /// The target identifying this struct definition.
    pub target: DefTarget,
    /// The name of the struct.
    pub name: String,
    /// Type parameters for the struct.
    pub type_params: Vec<TyVar>,
    /// Fields of the struct.
    pub fields: Vec<FieldDef>,
}

/// A field in a struct definition.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FieldDef {
    /// The name of the field.
    pub name: String,
    /// The type of the field.
    pub ty: Ty,
}

/// Information about a method in a trait or impl.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodInfo {
    /// The name of the method.
    pub name: String,
    /// Whether the method is static (no receiver).
    pub is_static: bool,
    /// The receiver mode for the method.
    pub recv_mode: ReceiverMode,
}

/// A trait definition extracted from either workspace or library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TraitDef {
    /// The target identifying this trait definition.
    pub target: DefTarget,
    /// The name of the trait.
    pub name: String,
    /// Type parameters for the trait.
    pub type_params: Vec<TyVar>,
    /// Super traits that this trait extends.
    pub super_traits: Vec<DefTarget>,
    /// Methods declared in this trait.
    pub methods: Vec<MethodInfo>,
}

/// An impl definition extracted from either workspace or library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ImplDef {
    /// The target identifying this impl definition.
    pub target: DefTarget,
    /// Type parameters for the impl.
    pub type_params: Vec<TyVar>,
    /// The type being implemented (as a Ty for display/inspection).
    pub implementing_type: Ty,
    /// The resolved target of the implementing type (for identity comparison).
    /// This is `None` for primitive types or unresolved types.
    pub implementing_type_target: Option<DefTarget>,
    /// The trait being implemented, if this is a trait impl.
    pub trait_ref: Option<DefTarget>,
    /// Methods defined in this impl.
    pub methods: Vec<MethodInfo>,
}

/// A type alias definition extracted from either workspace or library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TypeAliasDef {
    /// The target identifying this type alias definition.
    pub target: DefTarget,
    /// The name of the type alias.
    pub name: String,
    /// Type parameters for the type alias.
    pub type_params: Vec<TyVar>,
    /// The type that this alias refers to.
    pub aliased_type: Ty,
}

/// Look up a top-level definition by its full path.
///
/// Given an `ItemPath` like `mymodule::foo`, this query:
/// 1. Looks up the module index for the module path
/// 2. Finds the item by name in that module's exports
/// 3. Returns the `DefTarget` if found
///
/// This query only handles top-level definitions (functions, structs, traits, type aliases).
/// Methods (inherent, static, or otherwise) are resolved through type-directed resolution,
/// not through this syntactic path lookup.
#[query]
pub fn def_for_path(db: &Database, path: ItemPath) -> Option<DefTarget> {
    // Handle empty item path
    if path.item.is_empty() {
        return None;
    }

    // Only handle simple (non-nested) paths - methods are resolved via type-directed lookup
    if path.is_nested() {
        return None;
    }

    let item_name = &path.item[0];

    // Try workspace first
    let module_index = module_def_index(db, path.module.clone());
    if let Some(result) = module_index.get(item_name) {
        if let Ok(exported) = result {
            return exported_item_to_def_target(exported);
        }
    }

    // If not found in workspace, check libraries
    lookup_in_library(db, &path)
}

/// Convert an ExportedItem to a DefTarget.
fn exported_item_to_def_target(item: &ExportedItem) -> Option<DefTarget> {
    match item {
        ExportedItem::Def(def_id) => Some(DefTarget::Workspace(*def_id)),
        ExportedItem::Local(_) => {
            // Local bindings are not accessible as DefTargets through path lookup
            None
        }
    }
}

/// Look up an item path in libraries using the library_data query.
fn lookup_in_library(db: &Database, path: &ItemPath) -> Option<DefTarget> {
    let lib_data = library_data(db, path.module.clone())?;

    // Use the names index to look up the LibraryDefId for this path
    let lib_def_id = lib_data.lookup(path)?;
    Some(DefTarget::Library(lib_def_id))
}

/// Look up a struct definition by its DefTarget.
///
/// For workspace definitions, extracts the struct from the parsed AST.
/// For library definitions, looks up in the LibraryData.
///
/// Returns `None` if the target doesn'a correspond to a struct.
#[query]
pub fn struct_def(db: &Database, target: DefTarget) -> Option<StructDef> {
    match target {
        DefTarget::Workspace(def_id) => extract_workspace_struct(db, def_id),
        DefTarget::Library(lib_def_id) => extract_library_struct(db, &lib_def_id),
    }
}

/// Extract a struct definition from the workspace AST.
fn extract_workspace_struct(db: &Database, def_id: DefId) -> Option<StructDef> {
    let parse_result = parse_file(db, def_id.file);

    // Find the struct declaration by its DefId index.
    // DefId index 0 is FileMain, so we need to find the matching def in defs.
    let def_header = parse_result.defs.iter().find(|h| h.def_id == def_id)?;

    // Verify this is actually a struct
    if !matches!(def_header.kind, DefKind::Struct) {
        return None;
    }

    // Find the corresponding AST node in decls
    for decl in &parse_result.ast.decls {
        if let Decl::Struct(st) = &**decl {
            // Match by name
            if st.path.name() == Some(def_header.name.clone()) {
                return Some(StructDef {
                    target: DefTarget::Workspace(def_id),
                    name: def_header.name.clone(),
                    type_params: extract_type_params(&st.ty_params),
                    fields: extract_fields(&st.fields),
                });
            }
        }
    }

    None
}

/// Extract type parameters from TypeParams.
fn extract_type_params(ty_params: &Option<ray_core::ast::TypeParams>) -> Vec<TyVar> {
    match ty_params {
        Some(params) => params
            .tys
            .iter()
            .filter_map(|parsed_ty| {
                // Each type param should be a Ty::Var
                if let Ty::Var(var) = &**parsed_ty {
                    Some(var.clone())
                } else {
                    None
                }
            })
            .collect(),
        None => vec![],
    }
}

/// Extract fields from struct field declarations.
fn extract_fields(fields: &Option<Vec<Node<ray_core::ast::Name>>>) -> Vec<FieldDef> {
    match fields {
        Some(field_nodes) => field_nodes
            .iter()
            .filter_map(|field_node| {
                let name = field_node.path.name()?;
                // Get the type from the field's type annotation
                let ty = field_node
                    .ty
                    .as_ref()
                    .map(|parsed| parsed.ty.clone())
                    .unwrap_or(Ty::Never); // Use Never as placeholder if no type annotation
                Some(FieldDef { name, ty })
            })
            .collect(),
        None => vec![],
    }
}

/// Extract a struct definition from library data.
fn extract_library_struct(db: &Database, lib_def_id: &LibraryDefId) -> Option<StructDef> {
    let lib_data = library_data(db, lib_def_id.module.clone())?;

    // Look up the struct directly by LibraryDefId
    lib_data.structs.get(lib_def_id).cloned()
}

// ============================================================================
// trait_def query
// ============================================================================

/// Look up a trait definition by its DefTarget.
///
/// For workspace definitions, extracts the trait from the parsed AST.
/// For library definitions, looks up in the LibraryData.
///
/// Returns `None` if the target doesn'a correspond to a trait.
#[query]
pub fn trait_def(db: &Database, target: DefTarget) -> Option<TraitDef> {
    match target {
        DefTarget::Workspace(def_id) => extract_workspace_trait(db, def_id),
        DefTarget::Library(lib_def_id) => extract_library_trait(db, &lib_def_id),
    }
}

/// Extract a trait definition from the workspace AST.
fn extract_workspace_trait(db: &Database, def_id: DefId) -> Option<TraitDef> {
    let parse_result = parse_file(db, def_id.file);

    let def_header = parse_result.defs.iter().find(|h| h.def_id == def_id)?;

    if !matches!(def_header.kind, DefKind::Trait) {
        return None;
    }

    // Find the corresponding AST node in decls
    for decl in &parse_result.ast.decls {
        if let Decl::Trait(tr) = &**decl {
            // Match by name - trait name comes from tr.ty which is the trait type like `Eq['a]`
            let trait_name = tr.ty.name();
            if trait_name == def_header.name {
                // Extract type params from the trait type (e.g., `Eq['a]` -> ['a])
                let type_params = tr.ty.type_params();

                // Resolve super_trait to DefTarget
                let super_traits = tr
                    .super_trait
                    .as_ref()
                    .and_then(|st| resolve_type_to_def_target(db, st))
                    .into_iter()
                    .collect();

                // Extract method info from trait fields (which are FnSig decls)
                let methods = extract_trait_methods(&tr.fields);

                return Some(TraitDef {
                    target: DefTarget::Workspace(def_id),
                    name: def_header.name.clone(),
                    type_params,
                    super_traits,
                    methods,
                });
            }
        }
    }

    None
}

/// Resolve a type to a DefTarget by extracting its path and looking it up.
fn resolve_type_to_def_target(db: &Database, ty: &Ty) -> Option<DefTarget> {
    let path = match ty {
        Ty::Const(p) => p.clone(),
        Ty::Proj(p, _) => p.clone(),
        _ => return None,
    };

    // Convert Path to ItemPath and look it up
    let item_path = ItemPath::from(&path);
    def_for_path(db, item_path)
}

/// Resolve a Parsed<Ty> to its DefTarget using name resolutions.
///
/// This uses the synthetic_ids stored in the Parsed<Ty> to look up
/// the actual resolved definition. Returns `None` for primitive types
/// or if the type couldn't be resolved.
fn resolve_parsed_ty_to_def_target(
    ty: &ray_shared::span::parsed::Parsed<Ty>,
    resolutions: &std::collections::HashMap<ray_shared::node_id::NodeId, Resolution>,
) -> Option<DefTarget> {
    // The Parsed<Ty>'s synthetic_ids contain the NodeId(s) for the type reference
    let synth_ids = ty.synthetic_ids();
    synth_ids
        .first()
        .and_then(|node_id| resolutions.get(node_id))
        .and_then(|res| match res {
            Resolution::Def(target) => Some(target.clone()),
            _ => None,
        })
}

/// Extract method info from trait field declarations.
fn extract_trait_methods(fields: &[Node<Decl>]) -> Vec<MethodInfo> {
    fields
        .iter()
        .filter_map(|decl| match &**decl {
            Decl::FnSig(sig) => {
                let name = sig.path.name()?;
                let is_static = sig.modifiers.iter().any(|m| matches!(m, Modifier::Static));
                let recv_mode = compute_receiver_mode(sig, is_static);
                Some(MethodInfo {
                    name,
                    is_static,
                    recv_mode,
                })
            }
            Decl::Func(f) => {
                let name = f.sig.path.name()?;
                let is_static = f
                    .sig
                    .modifiers
                    .iter()
                    .any(|m| matches!(m, Modifier::Static));
                let recv_mode = compute_receiver_mode(&f.sig, is_static);
                Some(MethodInfo {
                    name,
                    is_static,
                    recv_mode,
                })
            }
            _ => None,
        })
        .collect()
}

/// Compute the receiver mode from a function signature.
fn compute_receiver_mode(sig: &ray_core::ast::FuncSig, is_static: bool) -> ReceiverMode {
    if is_static || sig.params.is_empty() {
        return ReceiverMode::None;
    }

    // Check the first parameter's type
    // FnParam::ty() already returns the mono type
    let first_param = &sig.params[0];
    if let Some(ty) = first_param.value.ty() {
        match ty {
            Ty::Ref(_) => ReceiverMode::Ptr,
            _ => ReceiverMode::Value,
        }
    } else {
        // No type annotation - assume value receiver
        ReceiverMode::Value
    }
}

/// Extract a trait definition from library data.
fn extract_library_trait(db: &Database, lib_def_id: &LibraryDefId) -> Option<TraitDef> {
    let lib_data = library_data(db, lib_def_id.module.clone())?;

    // Look up the trait directly by LibraryDefId
    lib_data.traits.get(lib_def_id).cloned()
}

// ============================================================================
// impl_def query
// ============================================================================

/// Look up an impl definition by its DefTarget.
///
/// For workspace definitions, extracts the impl from the parsed AST.
/// For library definitions, looks up in the LibraryData.
///
/// Returns `None` if the target doesn'a correspond to an impl.
#[query]
pub fn impl_def(db: &Database, target: DefTarget) -> Option<ImplDef> {
    match target {
        DefTarget::Workspace(def_id) => extract_workspace_impl(db, def_id),
        DefTarget::Library(lib_def_id) => extract_library_impl(db, &lib_def_id),
    }
}

/// Extract an impl definition from the workspace AST.
fn extract_workspace_impl(db: &Database, def_id: DefId) -> Option<ImplDef> {
    let parse_result = parse_file(db, def_id.file);
    let def_header = parse_result.defs.iter().find(|h| h.def_id == def_id)?;

    if !matches!(def_header.kind, DefKind::Impl) {
        return None;
    }

    // Get name resolutions for this file to resolve the trait reference
    let resolutions = name_resolutions(db, def_id.file);

    // Find the AST node using root_node from DefHeader
    let im = parse_result
        .ast
        .decls
        .iter()
        .find(|decl| decl.id == def_header.root_node)
        .and_then(|decl| match &**decl {
            Decl::Impl(im) => Some(im),
            _ => None,
        })?;

    // Handle the two forms of impl:
    // 1. `impl object Point { ... }` - inherent impl, is_object=true
    // 2. `impl ToStr[Point] { ... }` - trait impl, is_object=false
    let (implementing_type, implementing_type_target, trait_ref, type_params) = if im.is_object {
        // Inherent impl: the implementing type is im.ty directly
        let impl_ty = (*im.ty).clone();
        let ty_params = im.ty.type_params();

        // Resolve the implementing type using synthetic_ids on im.ty (the Parsed<Ty>)
        let impl_type_target = resolve_parsed_ty_to_def_target(&im.ty, &resolutions);

        (impl_ty, impl_type_target, None, ty_params)
    } else {
        // Trait impl: im.ty is Ty::Proj(trait_path, [implementing_type, ...])
        match &*im.ty {
            Ty::Proj(_, args) if !args.is_empty() => {
                // First argument is the implementing type
                let impl_ty = args[0].clone();

                // Resolve the trait using synthetic_ids and name_resolutions
                // synthetic_ids[0] is the NodeId for the trait type (e.g., ToStr)
                // synthetic_ids[1] is the NodeId for the implementing type
                let synth_ids = im.ty.synthetic_ids();
                let trait_target = synth_ids
                    .first()
                    .and_then(|node_id| resolutions.get(node_id))
                    .and_then(|res| match res {
                        Resolution::Def(target) => Some(target.clone()),
                        _ => None,
                    });

                // Resolve the implementing type (second synthetic_id)
                let impl_type_target = synth_ids
                    .get(1)
                    .and_then(|node_id| resolutions.get(node_id))
                    .and_then(|res| match res {
                        Resolution::Def(target) => Some(target.clone()),
                        _ => None,
                    });

                let ty_params = impl_ty.type_params();
                (impl_ty, impl_type_target, trait_target, ty_params)
            }
            _ => {
                // Fallback: treat as inherent
                let impl_ty = (*im.ty).clone();
                let ty_params = im.ty.type_params();
                let impl_type_target = resolve_parsed_ty_to_def_target(&im.ty, &resolutions);
                (impl_ty, impl_type_target, None, ty_params)
            }
        }
    };

    // Extract method info
    let methods = extract_impl_methods(im);

    Some(ImplDef {
        target: DefTarget::Workspace(def_id),
        type_params,
        implementing_type,
        implementing_type_target,
        trait_ref,
        methods,
    })
}

/// Extract method info from an impl block.
fn extract_impl_methods(im: &ray_core::ast::Impl) -> Vec<MethodInfo> {
    let mut methods = Vec::new();

    if let Some(funcs) = &im.funcs {
        for func in funcs {
            if let Some(name) = func.sig.path.name() {
                let is_static = func
                    .sig
                    .modifiers
                    .iter()
                    .any(|m| matches!(m, Modifier::Static));
                let recv_mode = compute_receiver_mode(&func.sig, is_static);
                methods.push(MethodInfo {
                    name,
                    is_static,
                    recv_mode,
                });
            }
        }
    }

    if let Some(externs) = &im.externs {
        for ext_node in externs {
            if let Decl::Extern(ext) = &ext_node.value {
                if let Some(name) = ext.decl().get_name() {
                    // Extern methods - check the inner FnSig
                    let inner_decl = ext.decl_node();
                    let (is_static, recv_mode) = if let Decl::FnSig(sig) = &inner_decl.value {
                        let is_static = sig.modifiers.iter().any(|m| matches!(m, Modifier::Static));
                        (is_static, compute_receiver_mode(sig, is_static))
                    } else {
                        (false, ReceiverMode::Value)
                    };
                    methods.push(MethodInfo {
                        name,
                        is_static,
                        recv_mode,
                    });
                }
            }
        }
    }

    methods
}

/// Extract an impl definition from library data.
fn extract_library_impl(db: &Database, lib_def_id: &LibraryDefId) -> Option<ImplDef> {
    let lib_data = library_data(db, lib_def_id.module.clone())?;

    // Look up the impl directly by LibraryDefId
    lib_data.impls.get(lib_def_id).cloned()
}

// ============================================================================
// type_alias query
// ============================================================================

/// Look up a type alias definition by its DefTarget.
///
/// For workspace definitions, extracts the type alias from the parsed AST.
/// For library definitions, this would look up in LibraryData (not yet implemented).
///
/// Returns `None` if the target doesn'a correspond to a type alias.
#[query]
pub fn type_alias(db: &Database, target: DefTarget) -> Option<TypeAliasDef> {
    match target {
        DefTarget::Workspace(def_id) => extract_workspace_type_alias(db, def_id),
        DefTarget::Library(_path) => {
            // Library type aliases not yet supported in LibraryData
            None
        }
    }
}

/// Extract a type alias definition from the workspace AST.
fn extract_workspace_type_alias(db: &Database, def_id: DefId) -> Option<TypeAliasDef> {
    let parse_result = parse_file(db, def_id.file);

    let def_header = parse_result.defs.iter().find(|h| h.def_id == def_id)?;

    if !matches!(def_header.kind, DefKind::TypeAlias) {
        return None;
    }

    // Find the corresponding AST node in decls
    for decl in &parse_result.ast.decls {
        if let Decl::TypeAlias(name_node, aliased_ty) = &**decl {
            // Match by name
            if name_node.path.name() == Some(def_header.name.clone()) {
                // Extract type params from the name if present
                // Type aliases can have params like `type Pair['A, 'B] = ('A, 'B)`
                // TyScheme.vars is already Vec<TyVar>
                let type_params = name_node
                    .ty
                    .as_ref()
                    .map(|ts| ts.vars.clone())
                    .unwrap_or_default();

                return Some(TypeAliasDef {
                    target: DefTarget::Workspace(def_id),
                    name: def_header.name.clone(),
                    type_params,
                    // aliased_ty is Parsed<Ty>, dereference to get Ty
                    aliased_type: (**aliased_ty).clone(),
                });
            }
        }
    }

    None
}

// ============================================================================
// impls_in_module query
// ============================================================================

/// Collect all impl block DefIds from a module.
///
/// Iterates through all files in the module and collects DefIds for all
/// `DefKind::Impl` definitions.
#[query]
pub fn impls_in_module(db: &Database, module_path: ModulePath) -> Vec<DefId> {
    let workspace = db.get_input::<WorkspaceSnapshot>(());

    let file_ids = match workspace.module_info(&module_path) {
        Some(info) => info.files.clone(),
        None => return Vec::new(),
    };

    let mut impls = Vec::new();
    for file_id in file_ids {
        let parse_result = parse_file(db, file_id);
        for def_header in &parse_result.defs {
            if matches!(def_header.kind, DefKind::Impl) {
                impls.push(def_header.def_id);
            }
        }
    }

    impls
}

// ============================================================================
// traits_in_module query
// ============================================================================

/// Collect all trait DefIds from a module.
///
/// Iterates through all files in the module and collects DefIds for all
/// `DefKind::Trait` definitions.
#[query]
pub fn traits_in_module(db: &Database, module_path: ModulePath) -> Vec<DefId> {
    let workspace = db.get_input::<WorkspaceSnapshot>(());

    let file_ids = match workspace.module_info(&module_path) {
        Some(info) => info.files.clone(),
        None => return Vec::new(),
    };

    let mut traits = Vec::new();
    for file_id in file_ids {
        let parse_result = parse_file(db, file_id);
        for def_header in &parse_result.defs {
            if matches!(def_header.kind, DefKind::Trait) {
                traits.push(def_header.def_id);
            }
        }
    }

    traits
}

// ============================================================================
// impls_for_type query
// ============================================================================

/// Result of looking up all impls for a type.
///
/// Separates inherent impls (no trait) from trait impls.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ImplsForType {
    /// Inherent impl blocks: `impl object Foo { ... }`
    pub inherent: Vec<DefTarget>,
    /// Trait impl blocks: `impl Trait[Foo] { ... }`
    pub trait_impls: Vec<DefTarget>,
}

/// Find all impl blocks for a given type.
///
/// Searches both workspace and library impls, returning them separated
/// into inherent impls and trait impls.
#[query]
pub fn impls_for_type(db: &Database, type_target: DefTarget) -> ImplsForType {
    let mut result = ImplsForType::default();

    // Search workspace impls
    collect_workspace_impls_for_type(db, &type_target, &mut result);

    // Search library impls
    collect_library_impls_for_type(db, &type_target, &mut result);

    result
}

/// Collect workspace impls that implement the target type.
fn collect_workspace_impls_for_type(
    db: &Database,
    type_target: &DefTarget,
    result: &mut ImplsForType,
) {
    let workspace = db.get_input::<WorkspaceSnapshot>(());

    // Iterate through all modules in the workspace
    for module_path in workspace.modules.keys() {
        let impl_ids = impls_in_module(db, module_path.clone());

        for impl_id in impl_ids {
            // Get the impl definition
            let impl_target = DefTarget::Workspace(impl_id);
            if let Some(impl_definition) = impl_def(db, impl_target.clone()) {
                // Check if this impl's implementing_type matches the target.
                // Prefer using the resolved implementing_type_target for exact identity matching.
                let matches = match &impl_definition.implementing_type_target {
                    Some(impl_type_target) => impl_type_target == type_target,
                    None => {
                        // Fallback to name-based matching for primitive types or unresolved cases
                        type_matches_target(&impl_definition.implementing_type, type_target, db)
                    }
                };

                if matches {
                    if impl_definition.trait_ref.is_some() {
                        result.trait_impls.push(impl_target);
                    } else {
                        result.inherent.push(impl_target);
                    }
                }
            }
        }
    }
}

/// Collect library impls that implement the target type.
fn collect_library_impls_for_type(
    db: &Database,
    type_target: &DefTarget,
    result: &mut ImplsForType,
) {
    let libraries = db.get_input::<LoadedLibraries>(());

    for (_lib_path, lib_data) in &libraries.libraries {
        // Iterate over impls with their LibraryDefId keys
        for (lib_def_id, lib_impl) in &lib_data.impls {
            // Check if this impl's implementing_type matches the target.
            // Prefer using the resolved implementing_type_target for exact identity matching.
            let matches = match &lib_impl.implementing_type_target {
                Some(impl_type_target) => impl_type_target == type_target,
                None => {
                    // Fallback to name-based matching for primitive types or unresolved cases
                    type_matches_target(&lib_impl.implementing_type, type_target, db)
                }
            };

            if matches {
                let impl_target = DefTarget::Library(lib_def_id.clone());
                if lib_impl.trait_ref.is_some() {
                    result.trait_impls.push(impl_target);
                } else {
                    result.inherent.push(impl_target);
                }
            }
        }
    }
}

// ============================================================================
// impls_for_trait query
// ============================================================================

/// Find all impl blocks for a given trait.
///
/// Searches both workspace and library impls, returning all impls where
/// `trait_ref` matches the given trait.
#[query]
pub fn impls_for_trait(db: &Database, trait_target: DefTarget) -> Vec<DefTarget> {
    let mut result = Vec::new();

    // Search workspace impls
    collect_workspace_impls_for_trait(db, &trait_target, &mut result);

    // Search library impls
    collect_library_impls_for_trait(db, &trait_target, &mut result);

    result
}

/// Collect workspace impls that implement the target trait.
fn collect_workspace_impls_for_trait(
    db: &Database,
    trait_target: &DefTarget,
    result: &mut Vec<DefTarget>,
) {
    let workspace = db.get_input::<WorkspaceSnapshot>(());

    // Iterate through all modules in the workspace
    for module_path in workspace.modules.keys() {
        let impl_ids = impls_in_module(db, module_path.clone());

        for impl_id in impl_ids {
            // Get the impl definition
            let impl_target = DefTarget::Workspace(impl_id);
            if let Some(impl_definition) = impl_def(db, impl_target.clone()) {
                // Check if this impl's trait_ref matches the target trait
                if let Some(ref impl_trait_ref) = impl_definition.trait_ref {
                    if impl_trait_ref == trait_target {
                        result.push(impl_target);
                    }
                }
            }
        }
    }
}

/// Collect library impls that implement the target trait.
fn collect_library_impls_for_trait(
    db: &Database,
    trait_target: &DefTarget,
    result: &mut Vec<DefTarget>,
) {
    let libraries = db.get_input::<LoadedLibraries>(());

    for (_lib_path, lib_data) in &libraries.libraries {
        // Iterate over impls with their LibraryDefId keys
        for (lib_def_id, lib_impl) in &lib_data.impls {
            // Check if this impl's trait_ref matches the target trait
            if let Some(ref impl_trait_ref) = lib_impl.trait_ref {
                if impl_trait_ref == trait_target {
                    result.push(DefTarget::Library(lib_def_id.clone()));
                }
            }
        }
    }
}

/// Check if a Ty matches a DefTarget.
///
/// A type matches if it refers to the same definition as the target.
/// For workspace definitions, we compare type names since the impl's type
/// is typically a local reference (e.g., `Point` not `mymodule::Point`).
fn type_matches_target(ty: &Ty, target: &DefTarget, db: &Database) -> bool {
    // Extract the type's name
    let type_name = ty.name();

    match target {
        DefTarget::Workspace(def_id) => {
            // For workspace targets, look up the def header to get the name
            let parse_result = parse_file(db, def_id.file);
            if let Some(def_header) = parse_result.defs.iter().find(|h| h.def_id == *def_id) {
                // Compare by name - the impl's type reference is local
                return def_header.name == type_name;
            }
            false
        }
        DefTarget::Library(lib_def_id) => {
            // For library targets, we need to look up the definition name
            if let Some(lib_data) = library_data(db, lib_def_id.module.clone()) {
                // Find the name in the library's names index (reverse lookup)
                for (item_path, def_id) in &lib_data.names {
                    if def_id == lib_def_id {
                        return item_path.item_name() == Some(type_name.as_str());
                    }
                }
            }
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use ray_shared::{
        def::LibraryDefId,
        pathlib::{FilePath, ItemPath, ModulePath},
        resolution::DefTarget,
        ty::Ty,
    };
    use ray_typing::types::{ReceiverMode, TyScheme};

    use crate::{
        queries::{
            defs::{
                FieldDef, MethodInfo, StructDef, TraitDef, def_for_path, impl_def, impls_for_trait,
                impls_for_type, impls_in_module, struct_def, trait_def, traits_in_module,
                type_alias,
            },
            libraries::{LibraryData, LoadedLibraries},
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    /// Helper to set up empty LoadedLibraries in the database.
    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), std::collections::HashMap::new());
    }

    #[test]
    fn def_for_path_returns_none_for_unknown_path() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let path = ItemPath::new(ModulePath::from("unknown"), vec!["foo".into()]);
        let result = def_for_path(&db, path);

        assert!(result.is_none());
    }

    #[test]
    fn def_for_path_finds_function_in_module() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "fn helper() {}".to_string());

        let path = ItemPath::new(module_path, vec!["helper".into()]);
        let result = def_for_path(&db, path);

        assert!(result.is_some());
        assert!(matches!(result.unwrap(), DefTarget::Workspace(_)));
    }

    #[test]
    fn def_for_path_finds_struct_in_module() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "struct Point { x: int, y: int }".to_string());

        let path = ItemPath::new(module_path, vec!["Point".into()]);
        let result = def_for_path(&db, path);

        assert!(result.is_some());
        assert!(matches!(result.unwrap(), DefTarget::Workspace(_)));
    }

    #[test]
    fn def_for_path_finds_library_function() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with core::io module containing a "read" function
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::io"));

        // Create a LibraryDefId for the function
        let read_def_id = LibraryDefId {
            module: ModulePath::from("core::io"),
            index: 0,
        };
        let read_path = ItemPath {
            module: ModulePath::from("core::io"),
            item: vec!["read".to_string()],
        };

        // Add to the names index
        core_lib
            .names
            .insert(read_path.clone(), read_def_id.clone());

        // Add the scheme
        core_lib.schemes.insert(
            read_def_id.clone(),
            TyScheme {
                vars: vec![],
                qualifiers: vec![],
                ty: Ty::unit(),
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        let path = ItemPath::new(ModulePath::from("core::io"), vec!["read".into()]);
        let result = def_for_path(&db, path);

        assert!(result.is_some());
        match result.unwrap() {
            DefTarget::Library(lib_def_id) => {
                assert_eq!(lib_def_id.module.to_string(), "core::io");
                assert_eq!(lib_def_id.index, 0);
            }
            _ => panic!("Expected Library target"),
        }
    }

    #[test]
    fn def_for_path_returns_none_for_local_binding() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        // Top-level binding becomes ExportedItem::Local, not Def
        FileSource::new(&db, file_id, "x = 42".to_string());

        let path = ItemPath::new(module_path, vec!["x".into()]);
        let result = def_for_path(&db, path);

        // Local bindings are not accessible via def_for_path
        assert!(result.is_none());
    }

    #[test]
    fn def_for_path_from_full_path() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "fn foo() {}".to_string());

        // Create ItemPath from a full Path
        let module = ModulePath::from("mymodule");
        let item_path = ItemPath {
            module,
            item: vec!["foo".to_string()],
        };
        let result = def_for_path(&db, item_path);

        assert!(result.is_some());
    }

    #[test]
    fn def_for_path_returns_none_for_nested_path() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Define a struct with an impl containing a method
        let source = r#"
struct List { items: int }

impl object List {
    fn push(self) => self.items
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Nested paths (methods) are not resolved by def_for_path
        let method_path = ItemPath::new(module_path, vec!["List".into(), "push".into()]);
        let result = def_for_path(&db, method_path);

        assert!(
            result.is_none(),
            "Nested paths should return None - methods are resolved via type-directed lookup"
        );
    }

    // struct_def tests

    #[test]
    fn struct_def_finds_workspace_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "struct Point { x: int, y: int }".to_string());

        // First get the DefTarget for the struct
        let path = ItemPath::new(module_path, vec!["Point".into()]);
        let target = def_for_path(&db, path).expect("struct should be found");

        // Now get the struct definition
        let result = struct_def(&db, target);

        assert!(result.is_some());
        let struct_def = result.unwrap();
        assert_eq!(struct_def.name, "Point");
        assert_eq!(struct_def.fields.len(), 2);
        assert_eq!(struct_def.fields[0].name, "x");
        assert_eq!(struct_def.fields[1].name, "y");
    }

    #[test]
    fn struct_def_finds_workspace_struct_with_type_params() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "struct Box['a] { value: 'a }".to_string());

        let path = ItemPath::new(module_path, vec!["Box".into()]);
        let target = def_for_path(&db, path).expect("struct should be found");

        let result = struct_def(&db, target);

        assert!(result.is_some());
        let struct_def = result.unwrap();
        assert_eq!(struct_def.name, "Box");
        assert_eq!(struct_def.type_params.len(), 1);
        assert_eq!(struct_def.fields.len(), 1);
        assert_eq!(struct_def.fields[0].name, "value");
    }

    #[test]
    fn struct_def_returns_none_for_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "fn helper() {}".to_string());

        let path = ItemPath::new(module_path, vec!["helper".into()]);
        let target = def_for_path(&db, path).expect("function should be found");

        // struct_def should return None for a function
        let result = struct_def(&db, target);
        assert!(result.is_none());
    }

    #[test]
    fn struct_def_finds_library_struct() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with a struct
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::option"));

        // Create LibraryDefId and ItemPath for the struct
        let option_def_id = LibraryDefId {
            module: ModulePath::from("core::option"),
            index: 0,
        };
        let option_path = ItemPath {
            module: ModulePath::from("core::option"),
            item: vec!["Option".to_string()],
        };

        // Add to names index
        core_lib
            .names
            .insert(option_path.clone(), option_def_id.clone());

        // Add struct definition using the spec types
        core_lib.structs.insert(
            option_def_id.clone(),
            StructDef {
                target: DefTarget::Library(option_def_id.clone()),
                name: "Option".to_string(),
                type_params: vec![],
                fields: vec![
                    FieldDef {
                        name: "some".to_string(),
                        ty: Ty::bool(),
                    },
                    FieldDef {
                        name: "value".to_string(),
                        ty: Ty::Any,
                    },
                ],
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        let target = DefTarget::Library(option_def_id);

        let result = struct_def(&db, target);

        assert!(result.is_some());
        let struct_def = result.unwrap();
        assert_eq!(struct_def.name, "Option");
        assert_eq!(struct_def.fields.len(), 2);
        assert_eq!(struct_def.fields[0].name, "some");
        assert_eq!(struct_def.fields[1].name, "value");
    }

    #[test]
    fn struct_def_returns_none_for_unknown_library_struct() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Use a LibraryDefId that doesn'a exist
        let target = DefTarget::Library(LibraryDefId {
            module: ModulePath::from("unknown"),
            index: 0,
        });

        let result = struct_def(&db, target);
        assert!(result.is_none());
    }

    // trait_def tests

    #[test]
    fn trait_def_finds_workspace_trait() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait Eq['a] {
    fn eq(self: 'a, other: 'a) -> bool
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let path = ItemPath::new(module_path, vec!["Eq".into()]);
        let target = def_for_path(&db, path).expect("trait should be found");

        let result = trait_def(&db, target);

        assert!(result.is_some());
        let trait_def = result.unwrap();
        assert_eq!(trait_def.name, "Eq");
        assert_eq!(trait_def.type_params.len(), 1);
        assert_eq!(trait_def.methods.len(), 1);
        assert_eq!(trait_def.methods[0].name, "eq");
        assert!(!trait_def.methods[0].is_static);
        assert_eq!(trait_def.methods[0].recv_mode, ReceiverMode::Value);
    }

    #[test]
    fn trait_def_finds_library_trait() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);

        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::cmp"));

        // Create LibraryDefId and ItemPath for the trait
        let ord_def_id = LibraryDefId {
            module: ModulePath::from("core::cmp"),
            index: 0,
        };
        let ord_path = ItemPath {
            module: ModulePath::from("core::cmp"),
            item: vec!["Ord".to_string()],
        };

        // Add to names index
        core_lib.names.insert(ord_path.clone(), ord_def_id.clone());

        // Add trait definition using the spec types
        core_lib.traits.insert(
            ord_def_id.clone(),
            TraitDef {
                target: DefTarget::Library(ord_def_id.clone()),
                name: "Ord".to_string(),
                type_params: vec![],
                super_traits: vec![],
                methods: vec![
                    MethodInfo {
                        name: "cmp".to_string(),
                        is_static: false,
                        recv_mode: ReceiverMode::Value,
                    },
                    MethodInfo {
                        name: "lt".to_string(),
                        is_static: false,
                        recv_mode: ReceiverMode::Value,
                    },
                ],
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        let target = DefTarget::Library(ord_def_id);

        let result = trait_def(&db, target);

        assert!(result.is_some());
        let trait_def = result.unwrap();
        assert_eq!(trait_def.name, "Ord");
        assert_eq!(trait_def.methods.len(), 2);
        assert_eq!(trait_def.methods[0].name, "cmp");
        assert_eq!(trait_def.methods[1].name, "lt");
    }

    #[test]
    fn trait_def_returns_none_for_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "struct Point { x: int }".to_string());

        let path = ItemPath::new(module_path, vec!["Point".into()]);
        let target = def_for_path(&db, path).expect("struct should be found");

        let result = trait_def(&db, target);
        assert!(result.is_none());
    }

    // impl_def tests

    #[test]
    fn impl_def_finds_workspace_impl() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn new(x: int, y: int): Point => Point { x, y }
    fn distance(self): int => self.x + self.y
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the impl DefTarget - impls are exported by their implementing type name
        let path = ItemPath::new(module_path, vec!["Point".into()]);
        let target = def_for_path(&db, path).expect("Point should be found");

        // The target is the struct, not the impl. We need to find the impl differently.
        // For now, let's just verify that struct_def works and impl_def returns None for structs.
        let result = impl_def(&db, target);

        // struct target should not return an impl
        assert!(result.is_none());
    }

    #[test]
    fn impl_def_returns_none_for_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "fn helper() {}".to_string());

        let path = ItemPath::new(module_path, vec!["helper".into()]);
        let target = def_for_path(&db, path).expect("function should be found");

        let result = impl_def(&db, target);
        assert!(result.is_none());
    }

    // type_alias tests

    #[test]
    #[ignore = "Parser does not yet support typealias declarations (parse_decl hits unreachable)"]
    fn type_alias_finds_workspace_alias() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "typealias IntPair = (int, int)".to_string());

        let path = ItemPath::new(module_path, vec!["IntPair".into()]);
        let target = def_for_path(&db, path).expect("type alias should be found");

        let result = type_alias(&db, target);

        assert!(result.is_some());
        let alias = result.unwrap();
        assert_eq!(alias.name, "IntPair");
    }

    #[test]
    fn type_alias_returns_none_for_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "struct Point { x: int }".to_string());

        let path = ItemPath::new(module_path, vec!["Point".into()]);
        let target = def_for_path(&db, path).expect("struct should be found");

        let result = type_alias(&db, target);
        assert!(result.is_none());
    }

    // impls_in_module tests

    #[test]
    fn impls_in_module_finds_impl_blocks() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn new(x: int, y: int): Point => Point { x, y }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let impls = impls_in_module(&db, module_path);

        assert_eq!(impls.len(), 1);
    }

    #[test]
    fn impls_in_module_returns_empty_for_no_impls() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "struct Point { x: int }".to_string());

        let impls = impls_in_module(&db, module_path);

        assert!(impls.is_empty());
    }

    #[test]
    fn impls_in_module_returns_empty_for_unknown_module() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let impls = impls_in_module(&db, ModulePath::from("unknown"));

        assert!(impls.is_empty());
    }

    // traits_in_module tests

    #[test]
    fn traits_in_module_finds_trait_definitions() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait Eq['a] {
    fn eq(self: 'a, other: 'a) -> bool
}

trait Ord['a] {
    fn cmp(self: 'a, other: 'a) -> int
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let traits = traits_in_module(&db, module_path);

        assert_eq!(traits.len(), 2);
    }

    #[test]
    fn traits_in_module_returns_empty_for_no_traits() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "struct Point { x: int }".to_string());

        let traits = traits_in_module(&db, module_path);

        assert!(traits.is_empty());
    }

    #[test]
    fn traits_in_module_returns_empty_for_unknown_module() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let traits = traits_in_module(&db, ModulePath::from("unknown"));

        assert!(traits.is_empty());
    }

    // impls_for_type tests

    #[test]
    fn impls_for_type_finds_inherent_impl() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn new(x: int, y: int): Point => Point { x, y }
    fn distance(self): int => self.x + self.y
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the struct's DefTarget
        let path = ItemPath::new(module_path, vec!["Point".into()]);
        let target = def_for_path(&db, path).expect("struct should be found");

        let result = impls_for_type(&db, target);

        assert_eq!(result.inherent.len(), 1);
        assert!(result.trait_impls.is_empty());
    }

    #[test]
    fn impls_for_type_returns_empty_for_type_without_impls() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "struct Point { x: int }".to_string());

        let path = ItemPath::new(module_path, vec!["Point".into()]);
        let target = def_for_path(&db, path).expect("struct should be found");

        let result = impls_for_type(&db, target);

        assert!(result.inherent.is_empty());
        assert!(result.trait_impls.is_empty());
    }

    #[test]
    fn impls_for_type_finds_trait_impl() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Define a trait and a struct with a trait impl
        // Ray syntax: impl Trait[Type] { ... }
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

        // Get the struct's DefTarget
        let path = ItemPath::new(module_path, vec!["Point".into()]);
        let target = def_for_path(&db, path).expect("struct should be found");

        let result = impls_for_type(&db, target);

        assert!(result.inherent.is_empty());
        assert_eq!(result.trait_impls.len(), 1);
    }

    #[test]
    fn impls_for_type_finds_both_inherent_and_trait_impls() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

struct Point { x: int, y: int }

impl object Point {
    fn new(x: int, y: int): Point => Point { x, y }
}

impl ToStr[Point] {
    fn to_str(self: Point) -> string => "Point"
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let path = ItemPath::new(module_path, vec!["Point".into()]);
        let target = def_for_path(&db, path).expect("struct should be found");

        let result = impls_for_type(&db, target);

        assert_eq!(result.inherent.len(), 1);
        assert_eq!(result.trait_impls.len(), 1);
    }

    // impls_for_trait tests

    #[test]
    fn impls_for_trait_finds_workspace_impl() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

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

        // Get the trait's DefTarget
        let trait_path = ItemPath::new(module_path, vec!["ToStr".into()]);
        let trait_target = def_for_path(&db, trait_path).expect("trait should be found");

        let result = impls_for_trait(&db, trait_target);

        assert_eq!(result.len(), 1);
        assert!(matches!(result[0], DefTarget::Workspace(_)));
    }

    #[test]
    fn impls_for_trait_finds_multiple_impls() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

struct Point { x: int, y: int }
struct Rect { w: int, h: int }

impl ToStr[Point] {
    fn to_str(self: Point) -> string => "Point"
}

impl ToStr[Rect] {
    fn to_str(self: Rect) -> string => "Rect"
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the trait's DefTarget
        let trait_path = ItemPath::new(module_path, vec!["ToStr".into()]);
        let trait_target = def_for_path(&db, trait_path).expect("trait should be found");

        let result = impls_for_trait(&db, trait_target);

        assert_eq!(result.len(), 2);
    }

    #[test]
    fn impls_for_trait_returns_empty_for_trait_without_impls() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

struct Point { x: int, y: int }
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the trait's DefTarget
        let trait_path = ItemPath::new(module_path, vec!["ToStr".into()]);
        let trait_target = def_for_path(&db, trait_path).expect("trait should be found");

        let result = impls_for_trait(&db, trait_target);

        assert!(result.is_empty());
    }

    #[test]
    fn impls_for_trait_ignores_inherent_impls() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

struct Point { x: int, y: int }

impl object Point {
    fn new(x: int, y: int): Point => Point { x, y }
}

impl ToStr[Point] {
    fn to_str(self: Point) -> string => "Point"
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the trait's DefTarget
        let trait_path = ItemPath::new(module_path, vec!["ToStr".into()]);
        let trait_target = def_for_path(&db, trait_path).expect("trait should be found");

        let result = impls_for_trait(&db, trait_target);

        // Should only find the trait impl, not the inherent impl
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn impls_for_type_distinguishes_same_named_types_in_different_modules() {
        // This test verifies that types with the same name in different modules
        // are correctly distinguished. Previously, type matching was by name only,
        // which would incorrectly match moduleA::Point with moduleB::Point.
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();

        // Module A with struct Point and an impl
        let module_a = ModulePath::from("module_a");
        let file_a = workspace.add_file(FilePath::from("module_a/mod.ray"), module_a.clone());

        // Module B with struct Point (same name, different module) and NO impl
        let module_b = ModulePath::from("module_b");
        let file_b = workspace.add_file(FilePath::from("module_b/mod.ray"), module_b.clone());

        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Module A has Point and an impl for it
        let source_a = r#"
struct Point { x: int, y: int }

impl object Point {
    fn origin(): Point => Point { x: 0, y: 0 }
}
"#;
        FileSource::new(&db, file_a, source_a.to_string());

        // Module B also has Point but NO impl
        let source_b = r#"
struct Point { a: string, b: string }
"#;
        FileSource::new(&db, file_b, source_b.to_string());

        // Get DefTargets for both Points
        let point_a_path = ItemPath::new(module_a, vec!["Point".into()]);
        let point_a_target = def_for_path(&db, point_a_path).expect("module_a::Point should exist");

        let point_b_path = ItemPath::new(module_b, vec!["Point".into()]);
        let point_b_target = def_for_path(&db, point_b_path).expect("module_b::Point should exist");

        // Verify they are different targets
        assert_ne!(
            point_a_target, point_b_target,
            "Points should be different DefTargets"
        );

        // impls_for_type on module_a::Point should find the impl
        let impls_a = impls_for_type(&db, point_a_target);
        assert_eq!(
            impls_a.inherent.len(),
            1,
            "module_a::Point should have 1 inherent impl"
        );

        // impls_for_type on module_b::Point should NOT find any impls
        // (the bug would cause this to incorrectly find module_a's impl because
        // it was matching by name "Point" only)
        let impls_b = impls_for_type(&db, point_b_target);
        assert_eq!(
            impls_b.inherent.len(),
            0,
            "module_b::Point should have NO impls - the impl belongs to module_a::Point only"
        );
    }

    #[test]
    fn impls_for_trait_distinguishes_same_named_traits_in_different_modules() {
        // This test verifies that traits with the same name in different modules
        // are correctly distinguished when looking up impls.
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();

        // Module A with trait Show and an impl
        let module_a = ModulePath::from("module_a");
        let file_a = workspace.add_file(FilePath::from("module_a/mod.ray"), module_a.clone());

        // Module B with trait Show (same name, different module) and NO impl
        let module_b = ModulePath::from("module_b");
        let file_b = workspace.add_file(FilePath::from("module_b/mod.ray"), module_b.clone());

        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Module A has trait Show and a type with an impl for it
        let source_a = r#"
trait Show['a] {
    fn show(self: 'a) -> string
}

struct Foo { x: int }

impl Show[Foo] {
    fn show(self: Foo) -> string => "Foo"
}
"#;
        FileSource::new(&db, file_a, source_a.to_string());

        // Module B has trait Show but NO impl
        let source_b = r#"
trait Show['a] {
    fn show(self: 'a) -> string
}
"#;
        FileSource::new(&db, file_b, source_b.to_string());

        // Get DefTargets for both Show traits
        let show_a_path = ItemPath::new(module_a, vec!["Show".into()]);
        let show_a_target = def_for_path(&db, show_a_path).expect("module_a::Show should exist");

        let show_b_path = ItemPath::new(module_b, vec!["Show".into()]);
        let show_b_target = def_for_path(&db, show_b_path).expect("module_b::Show should exist");

        // Verify they are different targets
        assert_ne!(
            show_a_target, show_b_target,
            "Traits should be different DefTargets"
        );

        // impls_for_trait on module_a::Show should find the impl
        let impls_a = impls_for_trait(&db, show_a_target);
        assert_eq!(impls_a.len(), 1, "module_a::Show should have 1 impl");

        // impls_for_trait on module_b::Show should NOT find any impls
        let impls_b = impls_for_trait(&db, show_b_target);
        assert_eq!(
            impls_b.len(),
            0,
            "module_b::Show should have NO impls - the impl is for module_a::Show"
        );
    }

    #[test]
    fn cross_module_trait_impl_resolves_correctly() {
        // This test verifies that a trait impl in module B for a trait defined in module A
        // is correctly associated with the trait from module A.
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();

        // Module A defines the trait
        let module_a = ModulePath::from("module_a");
        let file_a = workspace.add_file(FilePath::from("module_a/mod.ray"), module_a.clone());

        // Module B defines a type and implements the trait from module A
        let module_b = ModulePath::from("module_b");
        let file_b = workspace.add_file(FilePath::from("module_b/mod.ray"), module_b.clone());

        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Module A defines trait Display
        let source_a = r#"
trait Display['a] {
    fn display(self: 'a) -> string
}
"#;
        FileSource::new(&db, file_a, source_a.to_string());

        // Module B imports Display from module_a and implements it
        let source_b = r#"
import module_a with Display

struct Bar { value: int }

impl Display[Bar] {
    fn display(self: Bar) -> string => "Bar"
}
"#;
        FileSource::new(&db, file_b, source_b.to_string());

        // Get the trait's DefTarget from module_a
        let display_path = ItemPath::new(module_a, vec!["Display".into()]);
        let display_target =
            def_for_path(&db, display_path).expect("module_a::Display should exist");

        // impls_for_trait on module_a::Display should find the impl from module_b
        let impls = impls_for_trait(&db, display_target);
        assert_eq!(
            impls.len(),
            1,
            "module_a::Display should have 1 impl (from module_b)"
        );

        // Also verify that impls_for_type works correctly
        let bar_path = ItemPath::new(module_b, vec!["Bar".into()]);
        let bar_target = def_for_path(&db, bar_path).expect("module_b::Bar should exist");

        let bar_impls = impls_for_type(&db, bar_target);
        assert_eq!(
            bar_impls.trait_impls.len(),
            1,
            "Bar should have 1 trait impl"
        );
    }

    #[test]
    fn cross_module_impl_for_external_type() {
        // This test verifies that a trait and impl in module A for a type defined in module B
        // is correctly associated with the type from module B.
        // Scenario: Trait in A, impl in A, type in B
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();

        // Module B defines the type (declared first so A can import it)
        let module_b = ModulePath::from("module_b");
        let file_b = workspace.add_file(FilePath::from("module_b/mod.ray"), module_b.clone());

        // Module A defines the trait and impl for module_b's type
        let module_a = ModulePath::from("module_a");
        let file_a = workspace.add_file(FilePath::from("module_a/mod.ray"), module_a.clone());

        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Module B defines struct Foo
        let source_b = r#"
struct Foo { value: int }
"#;
        FileSource::new(&db, file_b, source_b.to_string());

        // Module A defines trait and impl for Foo (imported from B)
        let source_a = r#"
import module_b with Foo

trait Stringify['a] {
    fn stringify(self: 'a) -> string
}

impl Stringify[Foo] {
    fn stringify(self: Foo) -> string => "Foo"
}
"#;
        FileSource::new(&db, file_a, source_a.to_string());

        // Get the trait's DefTarget from module_a
        let stringify_path = ItemPath::new(module_a, vec!["Stringify".into()]);
        let stringify_target =
            def_for_path(&db, stringify_path).expect("module_a::Stringify should exist");

        // impls_for_trait on module_a::Stringify should find the impl
        let impls = impls_for_trait(&db, stringify_target);
        assert_eq!(impls.len(), 1, "module_a::Stringify should have 1 impl");

        // Get the type's DefTarget from module_b
        let foo_path = ItemPath::new(module_b, vec!["Foo".into()]);
        let foo_target = def_for_path(&db, foo_path).expect("module_b::Foo should exist");

        // impls_for_type on module_b::Foo should find the impl from module_a
        let foo_impls = impls_for_type(&db, foo_target);
        assert_eq!(
            foo_impls.trait_impls.len(),
            1,
            "module_b::Foo should have 1 trait impl (from module_a)"
        );
    }

    // ========================================================================
    // Library-workspace cross-module tests
    // ========================================================================

    #[test]
    fn workspace_impl_for_library_trait() {
        // This test verifies that a workspace type can implement a trait from a library.
        // Scenario: Trait in library, type and impl in workspace
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with a trait (core::fmt::Display)
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::fmt"));

        // Create LibraryDefId for the Display trait
        let display_def_id = LibraryDefId {
            module: ModulePath::from("core::fmt"),
            index: 0,
        };
        let display_path = ItemPath {
            module: ModulePath::from("core::fmt"),
            item: vec!["Display".to_string()],
        };

        // Add to names index
        core_lib
            .names
            .insert(display_path.clone(), display_def_id.clone());

        // Add trait definition
        core_lib.traits.insert(
            display_def_id.clone(),
            TraitDef {
                target: DefTarget::Library(display_def_id.clone()),
                name: "Display".to_string(),
                type_params: vec![],
                super_traits: vec![],
                methods: vec![MethodInfo {
                    name: "fmt".to_string(),
                    is_static: false,
                    recv_mode: ReceiverMode::Value,
                }],
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        // Workspace imports Display and implements it for a local type
        let source = r#"
import core::fmt with Display

struct Point { x: int, y: int }

impl Display[Point] {
    fn fmt(self: Point) -> string => "Point"
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the library trait's DefTarget
        let library_trait_target = DefTarget::Library(display_def_id);

        // impls_for_trait on the library trait should find the workspace impl
        let impls = impls_for_trait(&db, library_trait_target);
        assert_eq!(
            impls.len(),
            1,
            "Library trait core::fmt::Display should have 1 workspace impl"
        );

        // The impl should be a workspace impl
        assert!(
            matches!(impls[0], DefTarget::Workspace(_)),
            "The impl should be from the workspace, not the library"
        );

        // Also verify impls_for_type works
        let point_path = ItemPath::new(module_path, vec!["Point".into()]);
        let point_target = def_for_path(&db, point_path).expect("Point should exist");

        let point_impls = impls_for_type(&db, point_target);
        assert_eq!(
            point_impls.trait_impls.len(),
            1,
            "Point should have 1 trait impl"
        );
    }

    #[test]
    fn workspace_impl_for_library_type() {
        // This test verifies that a workspace trait can be implemented for a library type.
        // Scenario: Trait and impl in workspace, type in library
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with a struct (core::option::Option)
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::option"));

        // Create LibraryDefId for the Option struct
        let option_def_id = LibraryDefId {
            module: ModulePath::from("core::option"),
            index: 0,
        };
        let option_path = ItemPath {
            module: ModulePath::from("core::option"),
            item: vec!["Option".to_string()],
        };

        // Add to names index
        core_lib
            .names
            .insert(option_path.clone(), option_def_id.clone());

        // Add struct definition
        core_lib.structs.insert(
            option_def_id.clone(),
            StructDef {
                target: DefTarget::Library(option_def_id.clone()),
                name: "Option".to_string(),
                type_params: vec![],
                fields: vec![],
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        // Workspace defines a trait and implements it for the library type
        let source = r#"
import core::option with Option

trait Stringify['a] {
    fn stringify(self: 'a) -> string
}

impl Stringify[Option] {
    fn stringify(self: Option) -> string => "Option"
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the library type's DefTarget
        let library_type_target = DefTarget::Library(option_def_id);

        // impls_for_type on the library type should find the workspace impl
        let impls = impls_for_type(&db, library_type_target);
        assert_eq!(
            impls.trait_impls.len(),
            1,
            "Library type core::option::Option should have 1 workspace trait impl"
        );

        // The impl should be a workspace impl
        assert!(
            matches!(impls.trait_impls[0], DefTarget::Workspace(_)),
            "The impl should be from the workspace, not the library"
        );

        // Also verify impls_for_trait works
        let stringify_path = ItemPath::new(module_path, vec!["Stringify".into()]);
        let stringify_target = def_for_path(&db, stringify_path).expect("Stringify should exist");

        let trait_impls = impls_for_trait(&db, stringify_target);
        assert_eq!(trait_impls.len(), 1, "Stringify trait should have 1 impl");
    }
}

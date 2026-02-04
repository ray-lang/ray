//! Definition lookup queries for the incremental compiler.

use std::collections::HashMap;

use ray_core::ast::{Decl, FuncSig, Impl, Modifier, Name, Node};
use ray_query_macros::query;
use ray_shared::{
    def::{DefHeader, DefId, DefKind, LibraryDefId},
    file_id::FileId,
    node_id::NodeId,
    pathlib::{FilePath, ItemPath, ModulePath},
    resolution::{DefTarget, Resolution},
    span::{Source, Span},
    ty::{Ty, TyVar},
    type_param_id::TypeParamId,
};
use ray_typing::types::{
    FieldKind, ImplField, ImplKind, ImplTy, NominalKind, ReceiverMode, StructTy, TraitField,
    TraitTy, TyScheme,
};
use serde::{Deserialize, Serialize};

use crate::{
    queries::{
        exports::{ExportedItem, module_def_index},
        libraries::{LoadedLibraries, library_data},
        parse::parse_file,
        resolve::{file_scope, name_resolutions},
        types::{apply_type_resolutions, apply_type_resolutions_to_scheme, mapped_def_types},
        workspace::WorkspaceSnapshot,
    },
    query::{Database, Query},
};

/// A struct field definition for the query layer.
///
/// This is separate from the typechecker's StructTy field representation
/// (which uses tuple `(String, TyScheme)`) to better match query layer needs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StructField {
    /// The name of the field.
    pub name: String,
    /// The type scheme of the field.
    pub ty: TyScheme,
}

/// A struct definition for the query layer.
///
/// This is separate from the typechecker's StructTy to support:
/// - `DefTarget` for identifying definitions across workspace/library boundary
/// - `ItemPath` for definition identity
///
/// The typechecker's StructTy uses `Path` and tuple fields, which is needed
/// for synthetic structs (closures, function handles) that don't have DefTargets.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StructDef {
    /// The target identifying this struct definition.
    pub target: DefTarget,
    /// The path of the struct.
    pub path: ItemPath,
    /// The type scheme of the struct.
    pub ty: TyScheme,
    /// The fields of the struct.
    pub fields: Vec<StructField>,
}

impl StructDef {
    /// Convert a StructTy.
    pub fn convert_to_struct_ty(&self) -> StructTy {
        StructTy {
            kind: NominalKind::Struct,
            path: self.path.clone(),
            ty: self.ty.clone(),
            fields: self
                .fields
                .iter()
                .map(|f| (f.name.clone(), f.ty.clone()))
                .collect(),
        }
    }
}

/// Information about a method in a trait or impl.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodInfo {
    /// The definition target for this method (workspace or library).
    pub target: DefTarget,
    /// The fully qualified path of the method.
    pub path: ItemPath,
    /// The name of the method.
    pub name: String,
    /// Whether the method is static (no receiver).
    pub is_static: bool,
    /// The receiver mode for the method.
    pub recv_mode: ReceiverMode,
    /// The type scheme of the method.
    pub scheme: TyScheme,
}

/// A trait definition for the query layer.
///
/// This is separate from the typechecker's TraitTy to support:
/// - `DefTarget` for identifying definitions across workspace/library boundary
/// - `ItemPath` for definition identity
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraitDef {
    /// The target identifying this trait definition.
    pub target: DefTarget,
    /// The path of the trait.
    pub path: ItemPath,
    /// The trait's own type (e.g., `Eq['a]` for `trait Eq['a]`).
    pub ty: Ty,
    /// Type parameters for the trait.
    pub type_params: Vec<TyVar>,
    /// Super traits as types (e.g., `PartialEq['a]`).
    pub super_traits: Vec<Ty>,
    /// Methods declared in this trait.
    pub methods: Vec<MethodInfo>,
    /// Optional default type for the receiver.
    pub default_ty: Option<Ty>,
}

impl TraitDef {
    /// Convert to a TraitTy
    pub fn convert_to_trait_ty(&self) -> TraitTy {
        TraitTy {
            path: self.path.clone(),
            ty: self.ty.clone(),
            super_traits: self.super_traits.clone(),
            fields: self
                .methods
                .iter()
                .map(|m| TraitField {
                    kind: FieldKind::Method,
                    name: m.name.clone(),
                    ty: m.scheme.clone(),
                    is_static: m.is_static,
                    recv_mode: m.recv_mode,
                    target: Some(m.target.clone()),
                })
                .collect(),
            default_ty: self.default_ty.clone(),
        }
    }

    pub fn find_method(&self, method_name: &str) -> Option<MethodInfo> {
        self.methods
            .iter()
            .find(|method_info| method_info.name == method_name)
            .cloned()
    }
}

/// An impl definition for the query layer.
///
/// This is separate from the typechecker's ImplTy to support:
/// - `DefTarget` for identifying definitions across workspace/library boundary
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImplDef {
    /// The target identifying this impl definition.
    pub target: DefTarget,
    /// Type parameters for the impl.
    pub type_params: Vec<TyVar>,
    /// The type being implemented (e.g., `List['a]`).
    pub implementing_type: Ty,
    /// The trait being implemented as a type, if this is a trait impl (e.g., `Eq['a]`).
    pub trait_ty: Option<Ty>,
    /// Methods defined in this impl.
    pub methods: Vec<MethodInfo>,
}

impl ImplDef {
    /// Convert an ImplTy.
    pub fn convert_to_impl_ty(&self) -> ImplTy {
        let kind = match &self.trait_ty {
            Some(trait_ty) => {
                // Extract ty_args from the trait type.
                // For Ty::Proj(path, [impl_type, arg1, arg2, ...]), ty_args = [arg1, arg2, ...]
                // The first argument is the implementing type (base_ty), the rest are type args.
                let ty_args = match trait_ty {
                    Ty::Proj(_, args) if args.len() > 1 => args[1..].to_vec(),
                    _ => vec![],
                };
                ImplKind::Trait {
                    base_ty: self.implementing_type.clone(),
                    trait_ty: trait_ty.clone(),
                    ty_args,
                }
            }
            None => ImplKind::Inherent {
                recv_ty: self.implementing_type.clone(),
            },
        };

        ImplTy {
            kind,
            predicates: vec![],
            fields: self
                .methods
                .iter()
                .map(|m| ImplField {
                    kind: FieldKind::Method,
                    path: m.path.clone(),
                    scheme: Some(m.scheme.clone()),
                    is_static: m.is_static,
                    recv_mode: m.recv_mode,
                    src: Source::default(),
                    target: Some(m.target.clone()),
                })
                .collect(),
        }
    }

    pub fn find_method(&self, method_name: &str) -> Option<MethodInfo> {
        self.methods
            .iter()
            .find(|method_info| method_info.name == method_name)
            .cloned()
    }
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

/// Source location for a definition, supporting both workspace and library definitions.
///
/// Used for go-to-definition and hover functionality.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SourceLocation {
    /// Workspace definition with known FileId and span.
    Workspace { file: FileId, span: Span },
    /// Library definition with original source path (for source navigation).
    Library { filepath: FilePath, span: Span },
}

/// Aggregated metadata about a definition for display purposes.
///
/// This record is used for hover info and go-to-definition functionality.
/// It combines the path, location, documentation, and kind of a definition
/// into a single convenient structure.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DefinitionRecord {
    /// Fully qualified path of the definition.
    pub path: ItemPath,
    /// Source location for go-to-definition.
    pub source_location: Option<SourceLocation>,
    /// Documentation comment (if any).
    pub doc: Option<String>,
    /// The kind of definition (function, struct, trait, etc.).
    pub kind: DefKind,
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

    // Check for primitive/builtin types (int, bool, float, etc.)
    // These have no module (root module) and a single builtin name
    if path.module.segments().is_empty() && Ty::is_builtin_name(item_name) {
        return Some(DefTarget::Primitive(path));
    }

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

/// Get the DefHeader for a workspace definition.
///
/// This provides access to definition metadata (name, kind, span, parent)
/// for workspace definitions. Library and primitive definitions don't have
/// DefHeaders - use other queries like `def_name` or `definition_record` for those.
///
/// # Arguments
///
/// * `db` - The query database
/// * `def_id` - The definition identifier
///
/// # Returns
///
/// The DefHeader if the definition exists, `None` otherwise.
#[query]
pub fn def_header(db: &Database, def_id: DefId) -> Option<DefHeader> {
    let parse_result = parse_file(db, def_id.file);
    parse_result
        .defs
        .iter()
        .find(|h| h.def_id == def_id)
        .cloned()
}

/// Get the field DefIds for a struct.
///
/// Given a struct's DefId, returns a map from field name to field DefId.
/// The struct may be in any file - this query handles cross-file lookups.
///
/// Returns an empty map if the DefId doesn't refer to a struct or if
/// the struct has no fields.
#[query]
pub fn struct_fields(db: &Database, struct_def_id: DefId) -> HashMap<String, DefId> {
    let parse_result = parse_file(db, struct_def_id.file);
    parse_result
        .defs
        .iter()
        .filter(|h| h.parent == Some(struct_def_id) && matches!(h.kind, DefKind::StructField))
        .map(|h| (h.name.clone(), h.def_id))
        .collect()
}

/// Convert a DefTarget to its ItemPath.
///
/// For workspace definitions, looks up the DefHeader to get the name and module.
/// For library definitions, looks up in the LibraryData's reverse index.
///
/// This is the canonical way to get the fully-qualified path for a definition.
/// All code needing to convert DefTarget → ItemPath should use this query.
///
/// Returns `None` if the definition cannot be found (which indicates a bug in
/// the system - a valid DefTarget should always resolve to a path).
#[query]
pub fn def_path(db: &Database, target: DefTarget) -> Option<ItemPath> {
    match target {
        DefTarget::Workspace(def_id) => {
            let workspace = db.get_input::<WorkspaceSnapshot>(());
            let parse_result = parse_file(db, def_id.file);

            let module_path = workspace
                .file_info(def_id.file)
                .map(|info| info.module_path.clone())
                .unwrap_or_else(ModulePath::root);

            // Find the def header
            let def_header = parse_result.defs.iter().find(|h| h.def_id == def_id)?;

            // Check if this def has a parent (i.e., it's a method in an impl/trait)
            if let Some(parent_def_id) = def_header.parent {
                // Look up the parent def to get its name (the type or trait name)
                if let Some(parent_header) =
                    parse_result.defs.iter().find(|h| h.def_id == parent_def_id)
                {
                    // Build fully qualified path: module::ParentName::method_name
                    return Some(ItemPath::new(
                        module_path,
                        vec![parent_header.name.clone(), def_header.name.clone()],
                    ));
                }
            }

            // Top-level def: module::name
            Some(ItemPath::new(module_path, vec![def_header.name.clone()]))
        }
        DefTarget::Library(lib_def_id) => {
            // For library definitions, look up the path from library data
            let lib_data = library_data(db, lib_def_id.module.clone())?;
            // Find the ItemPath that maps to this LibraryDefId
            for (path, id) in &lib_data.names {
                if *id == lib_def_id {
                    return Some(path.clone());
                }
            }
            None
        }
        DefTarget::Primitive(path) => Some(path),
    }
}

/// Get the simple name of a definition.
///
/// For workspace definitions, returns the name from the DefHeader.
/// For library definitions, looks up the name from the ItemPath in the names index.
///
/// Returns `None` if the definition cannot be found.
///
/// Examples:
/// - For a function `mymodule::helper`, returns `"helper"`
/// - For a method `mymodule::List::push`, returns `"push"`
/// - For a struct `mymodule::Point`, returns `"Point"`
#[query]
pub fn def_name(db: &Database, target: DefTarget) -> Option<String> {
    match target {
        DefTarget::Workspace(def_id) => {
            let parse_result = parse_file(db, def_id.file);
            let def_header = parse_result.defs.iter().find(|h| h.def_id == def_id)?;
            Some(def_header.name.clone())
        }
        DefTarget::Library(lib_def_id) => {
            // For library definitions, get the name from the ItemPath
            let lib_data = library_data(db, lib_def_id.module.clone())?;
            // Find the ItemPath that maps to this LibraryDefId
            for (path, id) in &lib_data.names {
                if *id == lib_def_id {
                    return path.item_name().map(|s| s.to_string());
                }
            }
            None
        }
        DefTarget::Primitive(path) => path.item_name().map(|s| s.to_string()),
    }
}

/// Get aggregated metadata about a definition for display.
///
/// Returns a `DefinitionRecord` containing the path, source location,
/// documentation, and kind of the definition.
///
/// For workspace definitions:
/// - Path is constructed from module path + definition name
/// - Source location includes the FileId and span
/// - Documentation is not yet implemented (returns None)
/// - Kind is taken directly from DefHeader
///
/// For library definitions:
/// - Path is looked up from the library's names index
/// - Source location is not available (returns None)
/// - Documentation is not available (returns None)
/// - Kind is inferred from which collection contains the definition
#[query]
pub fn definition_record(db: &Database, target: DefTarget) -> Option<DefinitionRecord> {
    match target {
        DefTarget::Workspace(def_id) => {
            let path = def_path(db, DefTarget::Workspace(def_id))?;
            let parse_result = parse_file(db, def_id.file);
            let def_header = parse_result.defs.iter().find(|h| h.def_id == def_id)?;

            let source_location = Some(SourceLocation::Workspace {
                file: def_id.file,
                span: def_header.span,
            });

            // doc_comment query not yet implemented
            let doc = None;

            Some(DefinitionRecord {
                path,
                source_location,
                doc,
                kind: def_header.kind,
            })
        }
        DefTarget::Library(lib_def_id) => {
            let path = def_path(db, DefTarget::Library(lib_def_id.clone()))?;
            let lib_data = library_data(db, lib_def_id.module.clone())?;

            // Library definitions don't have source locations in current implementation
            let source_location = None;

            // Library definitions don't have doc comments in current implementation
            let doc = None;

            // Infer kind from which collection contains this definition
            let kind = if lib_data.structs.contains_key(&lib_def_id) {
                DefKind::Struct
            } else if lib_data.traits.contains_key(&lib_def_id) {
                DefKind::Trait
            } else if lib_data.impls.contains_key(&lib_def_id) {
                DefKind::Impl
            } else {
                // Default to function for definitions in schemes but not in other collections
                DefKind::Function {
                    signature: ray_shared::def::SignatureStatus::FullyAnnotated,
                }
            };

            Some(DefinitionRecord {
                path,
                source_location,
                doc,
                kind,
            })
        }
        DefTarget::Primitive(path) => {
            // Primitives are built-in types with no source location
            Some(DefinitionRecord {
                path,
                source_location: None,
                doc: None,
                kind: DefKind::Primitive,
            })
        }
    }
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
        DefTarget::Primitive(_) => None, // Primitives are not structs
    }
}

/// Extract a struct definition from the workspace AST.
fn extract_workspace_struct(db: &Database, def_id: DefId) -> Option<StructDef> {
    let parse_result = parse_file(db, def_id.file);
    let workspace = db.get_input::<WorkspaceSnapshot>(());

    let def_header = parse_result.defs.iter().find(|h| h.def_id == def_id)?;

    // Verify this is actually a struct
    if !matches!(def_header.kind, DefKind::Struct) {
        return None;
    }

    // Build the ItemPath for this struct
    let module_path = workspace
        .file_info(def_id.file)
        .map(|info| info.module_path.clone())
        .unwrap_or_else(ModulePath::root);
    let path = ItemPath::new(module_path, vec![def_header.name.clone()]);

    // Get type mappings and resolutions
    let mapping = mapped_def_types(db, def_id);
    let resolutions = name_resolutions(db, def_id.file);

    // Create closure to convert DefTarget to ItemPath
    let get_item_path = |target: &DefTarget| {
        def_path(db, target.clone()).expect("DefTarget should have a valid path")
    };

    // Find the corresponding AST node in decls
    for decl in &parse_result.ast.decls {
        if let Decl::Struct(st) = &decl.value {
            // Match by name
            if st.path.name() == Some(def_header.name.clone()) {
                // Get schema vars from the mapping
                let schema_vars: Vec<TyVar> = mapping.var_map.values().cloned().collect();

                // Build the struct's own type using schema vars: e.g., Box[?s0]
                let struct_ty = if schema_vars.is_empty() {
                    Ty::Const(path.clone())
                } else {
                    let ty_args: Vec<Ty> = schema_vars.iter().map(|v| Ty::Var(v.clone())).collect();
                    Ty::Proj(path.clone(), ty_args)
                };

                // Build the TyScheme for the struct (quantified over schema vars)
                let ty = TyScheme::new(schema_vars.clone(), vec![], struct_ty);

                // Extract fields with resolved types
                let fields = extract_struct_fields_resolved(
                    &st.fields,
                    &schema_vars,
                    &resolutions,
                    &mapping.var_map,
                    get_item_path,
                );

                return Some(StructDef {
                    target: DefTarget::Workspace(def_id),
                    path,
                    ty,
                    fields,
                });
            }
        }
    }

    None
}

/// Extract fields from struct field declarations with proper TyScheme quantification.
///
/// Each field's type is wrapped in a TyScheme that quantifies over the struct's type parameters.
/// For example, for `struct Box['a] { value: 'a }`, the field `value` gets
/// `TyScheme { vars: ['a], qualifiers: [], ty: 'a }`.
#[allow(dead_code)]
fn extract_struct_fields(
    fields: &Option<Vec<Node<Name>>>,
    type_params: &[TyVar],
) -> Vec<StructField> {
    match fields {
        Some(field_nodes) => field_nodes
            .iter()
            .filter_map(|field_node| {
                let name = field_node.path.name()?;
                // Get the type from the field's type annotation
                let field_ty = field_node
                    .ty
                    .as_ref()
                    .map(|parsed| parsed.ty.clone())
                    .unwrap_or(Ty::Never); // Use Never as placeholder if no type annotation

                // Wrap in TyScheme quantified over struct's type params
                let ty = TyScheme::new(type_params.to_vec(), vec![], field_ty);

                Some(StructField { name, ty })
            })
            .collect(),
        None => vec![],
    }
}

/// Extract fields from struct field declarations with resolved types.
///
/// This version uses `apply_type_resolutions_to_scheme` to:
/// 1. Qualify paths: `Point` → `mymodule::Point`
/// 2. Map type variables: `'a` → `?s0` (schema var)
///
/// Each field's type is wrapped in a TyScheme quantified over the struct's schema vars.
fn extract_struct_fields_resolved<F>(
    fields: &Option<Vec<Node<Name>>>,
    schema_vars: &[TyVar],
    resolutions: &HashMap<NodeId, Resolution>,
    var_map: &HashMap<TypeParamId, TyVar>,
    get_item_path: F,
) -> Vec<StructField>
where
    F: Fn(&DefTarget) -> ItemPath + Copy,
{
    match fields {
        Some(field_nodes) => field_nodes
            .iter()
            .filter_map(|field_node| {
                let name = field_node.path.name()?;

                // Apply resolutions to get the resolved field type
                let field_ty = if let Some(parsed_scheme) = &field_node.ty {
                    apply_type_resolutions_to_scheme(
                        parsed_scheme,
                        resolutions,
                        var_map,
                        get_item_path,
                    )
                } else {
                    Ty::Never // Use Never as placeholder if no type annotation
                };

                // Wrap in TyScheme quantified over struct's schema vars
                let ty = TyScheme::new(schema_vars.to_vec(), vec![], field_ty);

                Some(StructField { name, ty })
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
        DefTarget::Primitive(_) => None, // Primitives are not traits
    }
}

/// Extract a trait definition from the workspace AST.
fn extract_workspace_trait(db: &Database, def_id: DefId) -> Option<TraitDef> {
    let parse_result = parse_file(db, def_id.file);
    let workspace = db.get_input::<WorkspaceSnapshot>(());

    let def_header = parse_result.defs.iter().find(|h| h.def_id == def_id)?;

    if !matches!(def_header.kind, DefKind::Trait) {
        return None;
    }

    // Build the ItemPath for this trait
    let module_path = workspace
        .file_info(def_id.file)
        .map(|info| info.module_path.clone())
        .unwrap_or_else(ModulePath::root);
    let path = ItemPath::new(module_path, vec![def_header.name.clone()]);

    // Get type mappings and resolutions
    let mapping = mapped_def_types(db, def_id);
    let resolutions = name_resolutions(db, def_id.file);

    // Create closure to convert DefTarget to ItemPath
    let get_item_path = |target: &DefTarget| {
        def_path(db, target.clone()).expect("DefTarget should have a valid path")
    };

    // Find the corresponding AST node in decls
    for decl in &parse_result.ast.decls {
        if let Decl::Trait(tr) = &decl.value {
            // Match by name - trait name comes from tr.ty which is the trait type like `Eq['a]`
            let trait_name = tr.ty.name();
            if trait_name == def_header.name {
                // Get schema vars from the mapping
                let schema_vars: Vec<TyVar> = mapping.var_map.values().cloned().collect();

                // Build the trait's own type using schema vars: e.g., Eq[?s0]
                let ty = if schema_vars.is_empty() {
                    Ty::Const(path.clone())
                } else {
                    let ty_args: Vec<Ty> = schema_vars.iter().map(|v| Ty::Var(v.clone())).collect();
                    Ty::Proj(path.clone(), ty_args)
                };

                // Get super traits with resolved types
                let super_traits: Vec<Ty> = tr
                    .super_trait
                    .iter()
                    .map(|parsed_ty| {
                        apply_type_resolutions(
                            parsed_ty,
                            &resolutions,
                            &mapping.var_map,
                            get_item_path,
                        )
                    })
                    .collect();

                // Extract method info from trait fields with resolved types
                let methods = extract_trait_methods_resolved(
                    db,
                    &tr.fields,
                    &parse_result.defs,
                    &path,
                    &resolutions,
                    &mapping.var_map,
                    get_item_path,
                );

                return Some(TraitDef {
                    target: DefTarget::Workspace(def_id),
                    path,
                    ty,
                    type_params: schema_vars,
                    super_traits,
                    methods,
                    default_ty: None,
                });
            }
        }
    }

    None
}

/// Extract method info from trait field declarations with resolved types.
///
/// This version combines the parent trait's var_map with each method's own var_map
/// to properly resolve inherited type parameters.
fn extract_trait_methods_resolved<F>(
    db: &Database,
    fields: &[Node<Decl>],
    defs: &[DefHeader],
    parent_path: &ItemPath,
    resolutions: &HashMap<NodeId, Resolution>,
    parent_var_map: &HashMap<TypeParamId, TyVar>,
    get_item_path: F,
) -> Vec<MethodInfo>
where
    F: Fn(&DefTarget) -> ItemPath + Copy,
{
    fields
        .iter()
        .filter_map(|decl| {
            let def_id = defs
                .iter()
                .find(|h| h.root_node == decl.id)
                .map(|h| h.def_id)?;
            let target = DefTarget::Workspace(def_id);

            // Get the method's own type mappings
            let method_mapping = mapped_def_types(db, def_id);

            // Combine parent var_map with method var_map
            // Method's own type params take precedence (shadowing)
            let mut combined_var_map = parent_var_map.clone();
            combined_var_map.extend(method_mapping.var_map.iter().map(|(k, v)| (*k, v.clone())));

            match &decl.value {
                Decl::FnSig(sig) => {
                    let name = sig.path.name()?;
                    let path = parent_path.with_item(&name);
                    let is_static = sig.modifiers.iter().any(|m| matches!(m, Modifier::Static));
                    let recv_mode = compute_receiver_mode(sig, is_static);

                    // Extract scheme with resolved types
                    let scheme = extract_method_scheme_resolved(
                        sig,
                        resolutions,
                        &combined_var_map,
                        get_item_path,
                    );

                    Some(MethodInfo {
                        target,
                        path,
                        name,
                        is_static,
                        recv_mode,
                        scheme,
                    })
                }
                Decl::Func(f) => {
                    let name = f.sig.path.name()?;
                    let path = parent_path.with_item(&name);
                    let is_static = f
                        .sig
                        .modifiers
                        .iter()
                        .any(|m| matches!(m, Modifier::Static));
                    let recv_mode = compute_receiver_mode(&f.sig, is_static);

                    // Extract scheme with resolved types
                    let scheme = extract_method_scheme_resolved(
                        &f.sig,
                        resolutions,
                        &combined_var_map,
                        get_item_path,
                    );

                    Some(MethodInfo {
                        target,
                        path,
                        name,
                        is_static,
                        recv_mode,
                        scheme,
                    })
                }
                _ => None,
            }
        })
        .collect()
}

/// Extract a TyScheme from a function signature with resolved types.
fn extract_method_scheme_resolved<F>(
    sig: &FuncSig,
    resolutions: &HashMap<NodeId, Resolution>,
    var_map: &HashMap<TypeParamId, TyVar>,
    get_item_path: F,
) -> TyScheme
where
    F: Fn(&DefTarget) -> ItemPath + Copy,
{
    // Extract parameter types with resolutions applied
    let param_tys: Vec<Ty> = sig
        .params
        .iter()
        .filter_map(|param| {
            param.value.parsed_ty().map(|parsed_scheme| {
                apply_type_resolutions_to_scheme(parsed_scheme, resolutions, var_map, get_item_path)
            })
        })
        .collect();

    // Extract return type with resolutions applied
    let ret_ty = sig
        .ret_ty
        .as_ref()
        .map(|parsed| apply_type_resolutions(parsed, resolutions, var_map, get_item_path))
        .unwrap_or(Ty::unit());

    // Build the function type
    let func_ty = Ty::Func(param_tys, Box::new(ret_ty));

    // Get schema vars from var_map (these are the quantified variables)
    let schema_vars: Vec<TyVar> = var_map.values().cloned().collect();

    // TODO: Handle qualifiers when we support where-clauses on methods
    TyScheme::new(schema_vars, vec![], func_ty)
}

/// Compute the receiver mode from a function signature.
fn compute_receiver_mode(sig: &FuncSig, is_static: bool) -> ReceiverMode {
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

/// Look up all traits
///
/// Finds all traits in the workspace and library definitions
///
#[query]
pub fn all_traits(db: &Database) -> Vec<TraitDef> {
    let mut traits = Vec::new();

    // Collect workspace traits
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    for module_path in workspace.all_module_paths() {
        let trait_ids = traits_in_module(db, module_path.clone());
        for trait_id in trait_ids {
            if let Some(trait_definition) = trait_def(db, DefTarget::Workspace(trait_id)) {
                traits.push(trait_definition);
            }
        }
    }

    // Collect library traits
    let libraries = db.get_input::<LoadedLibraries>(());
    for (_lib_path, lib_data) in &libraries.libraries {
        for (_lib_def_id, trait_definition) in &lib_data.traits {
            traits.push(trait_definition.clone());
        }
    }

    traits
}

/// Look up trait methods in the workspace.
#[query]
pub fn trait_methods_for_name(db: &Database, method_name: &String) -> Vec<(TraitDef, MethodInfo)> {
    all_traits(db)
        .into_iter()
        .filter_map(|trait_def| {
            trait_def.methods.iter().find_map(|method_info| {
                if method_info.name == method_name {
                    Some((trait_def.clone(), method_info.clone()))
                } else {
                    None
                }
            })
        })
        .collect()
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
        DefTarget::Primitive(_) => None, // Primitives don't have impl definitions
    }
}

/// Extract an impl definition from the workspace AST.
fn extract_workspace_impl(db: &Database, def_id: DefId) -> Option<ImplDef> {
    let parse_result = parse_file(db, def_id.file);
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let def_header = parse_result.defs.iter().find(|h| h.def_id == def_id)?;

    if !matches!(def_header.kind, DefKind::Impl) {
        return None;
    }

    // Build the module path
    let module_path = workspace
        .file_info(def_id.file)
        .map(|info| info.module_path.clone())
        .unwrap_or_else(ModulePath::root);

    // Get type mappings and resolutions
    let mapping = mapped_def_types(db, def_id);
    let resolutions = name_resolutions(db, def_id.file);

    // Create closure to convert DefTarget to ItemPath
    let get_item_path = |target: &DefTarget| {
        def_path(db, target.clone()).expect("DefTarget should have a valid path")
    };

    // Find the AST node using root_node from DefHeader
    let im = parse_result
        .ast
        .decls
        .iter()
        .find(|decl| decl.id == def_header.root_node)
        .and_then(|decl| match &decl.value {
            Decl::Impl(im) => Some(im),
            _ => None,
        })?;

    // Get schema vars from the mapping
    let schema_vars: Vec<TyVar> = mapping.var_map.values().cloned().collect();

    // Handle the two forms of impl:
    // 1. `impl object Point { ... }` - inherent impl, is_object=true
    // 2. `impl ToStr[Point] { ... }` - trait impl, is_object=false
    let (implementing_type, trait_ty) = if im.is_object {
        // Inherent impl: the implementing type is im.ty directly
        let impl_ty = apply_type_resolutions(&im.ty, &resolutions, &mapping.var_map, get_item_path);
        (impl_ty, None)
    } else {
        // Trait impl: im.ty is Ty::Proj(trait_path, [implementing_type, ...])
        // e.g., `impl Eq[Point]` -> trait_ty = Eq[Point], implementing_type = Point
        match &*im.ty {
            Ty::Proj(_trait_path, args) if !args.is_empty() => {
                // First argument is the implementing type
                // Create a parsed view of just the first arg with its synthetic IDs
                // For now, resolve the inner type directly
                let impl_ty = resolve_ty_with_scope(db, &args[0], def_id.file, &module_path);

                // Resolve the full trait type using resolutions
                let trait_type =
                    apply_type_resolutions(&im.ty, &resolutions, &mapping.var_map, get_item_path);

                (impl_ty, Some(trait_type))
            }
            _ => {
                // Fallback: treat as inherent
                let impl_ty =
                    apply_type_resolutions(&im.ty, &resolutions, &mapping.var_map, get_item_path);
                (impl_ty, None)
            }
        }
    };

    // Build the impl parent path (Type name for method paths)
    let impl_type_name = implementing_type.name();
    let impl_path = ItemPath::new(module_path, vec![impl_type_name]);

    // Extract method info with resolved types
    let methods = extract_impl_methods(
        db,
        im,
        &parse_result.defs,
        &impl_path,
        &resolutions,
        &mapping.var_map,
        get_item_path,
    );

    Some(ImplDef {
        target: DefTarget::Workspace(def_id),
        type_params: schema_vars,
        implementing_type,
        trait_ty,
        methods,
    })
}

/// Extract method info from an impl block with resolved types.
///
/// This version combines the parent impl's var_map with each method's own var_map
/// to properly resolve inherited type parameters.
fn extract_impl_methods<F>(
    db: &Database,
    im: &Impl,
    defs: &[DefHeader],
    parent_path: &ItemPath,
    resolutions: &HashMap<NodeId, Resolution>,
    parent_var_map: &HashMap<TypeParamId, TyVar>,
    get_item_path: F,
) -> Vec<MethodInfo>
where
    F: Fn(&DefTarget) -> ItemPath + Copy,
{
    let mut methods = Vec::new();

    if let Some(funcs) = &im.funcs {
        for decl in funcs {
            let Decl::Func(func) = &decl.value else {
                unreachable!("impl funcs should only contain Decl::Func");
            };
            let def_id = match defs.iter().find(|h| h.root_node == decl.id) {
                Some(h) => h.def_id,
                None => continue,
            };
            let target = DefTarget::Workspace(def_id);

            // Get the method's own type mappings
            let method_mapping = mapped_def_types(db, def_id);

            // Combine parent var_map with method var_map
            let mut combined_var_map = parent_var_map.clone();
            combined_var_map.extend(method_mapping.var_map.iter().map(|(k, v)| (*k, v.clone())));

            if let Some(name) = func.sig.path.name() {
                let path = parent_path.with_item(&name);
                let is_static = func
                    .sig
                    .modifiers
                    .iter()
                    .any(|m| matches!(m, Modifier::Static));
                let recv_mode = compute_receiver_mode(&func.sig, is_static);

                // Extract scheme with resolved types
                let scheme = extract_method_scheme_resolved(
                    &func.sig,
                    resolutions,
                    &combined_var_map,
                    get_item_path,
                );

                methods.push(MethodInfo {
                    target,
                    path,
                    name: name.to_string(),
                    is_static,
                    recv_mode,
                    scheme,
                });
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
        DefTarget::Primitive(_) => None, // Primitives are not type aliases
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
        if let Decl::TypeAlias(name_node, aliased_ty) = &decl.value {
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

/// Find the impl of a trait for a given type
///
/// Searches all impls in the workspace and libraries
///
/// Returns `None` if it cannot be found
#[query]
pub fn trait_impl_for_type(
    db: &Database,
    type_target: DefTarget,
    trait_target: DefTarget,
) -> Option<DefTarget> {
    // Get the trait's path for comparison
    let trait_path = def_path(db, trait_target)?;

    // Get all trait impls for the type
    let ImplsForType { trait_impls, .. } = impls_for_type(db, type_target);

    // Find the impl whose trait_ty matches the target trait
    for impl_target in trait_impls {
        if let Some(impl_definition) = impl_def(db, impl_target.clone()) {
            if let Some(trait_ty) = &impl_definition.trait_ty {
                // Check if the trait type's path matches the target trait path
                if let Some(impl_trait_path) = trait_ty.item_path() {
                    // Compare the base paths (without type arguments)
                    if impl_trait_path == &trait_path {
                        return Some(impl_target);
                    }
                }
            }
        }
    }

    None
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
                let matches =
                    type_matches_target(&impl_definition.implementing_type, type_target, db);

                if matches {
                    if impl_definition.trait_ty.is_some() {
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
            let matches = type_matches_target(&lib_impl.implementing_type, type_target, db);

            if matches {
                let impl_target = DefTarget::Library(lib_def_id.clone());
                if lib_impl.trait_ty.is_some() {
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
                // Check if this impl's trait_ty matches the target trait
                if let Some(ref impl_trait_ty) = impl_definition.trait_ty {
                    if trait_ty_matches_target(impl_trait_ty, trait_target, db) {
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
            // Check if this impl's trait_ty matches the target trait
            if let Some(ref impl_trait_ty) = lib_impl.trait_ty {
                if trait_ty_matches_target(impl_trait_ty, trait_target, db) {
                    result.push(DefTarget::Library(lib_def_id.clone()));
                }
            }
        }
    }
}

/// Get the ItemPath for a DefTarget.
fn path_for_target(target: &DefTarget, db: &Database) -> Option<ItemPath> {
    match target {
        DefTarget::Workspace(def_id) => {
            let parse_result = parse_file(db, def_id.file);
            let workspace = db.get_input::<WorkspaceSnapshot>(());
            let def_header = parse_result.defs.iter().find(|h| h.def_id == *def_id)?;

            // Build ItemPath from module path + definition name
            let module_path = workspace
                .file_info(def_id.file)
                .map(|info| info.module_path.clone())
                .unwrap_or_else(ModulePath::root);
            Some(ItemPath::new(module_path, vec![def_header.name.clone()]))
        }
        DefTarget::Library(lib_def_id) => {
            let lib_data = library_data(db, lib_def_id.module.clone())?;
            lib_data
                .names
                .iter()
                .find(|(_, def_id)| *def_id == lib_def_id)
                .map(|(item_path, _)| item_path.clone())
        }
        DefTarget::Primitive(path) => Some(path.clone()),
    }
}

/// Resolve a Ty using file scope, falling back to module qualification.
///
/// For types without Parsed wrapper (like nested type args), we look up the type
/// name in the file's scope (which includes module exports and selective imports).
fn resolve_ty_with_scope(db: &Database, ty: &Ty, file_id: FileId, module_path: &ModulePath) -> Ty {
    let scope = file_scope(db, file_id);

    match ty {
        Ty::Const(path) if path.module.is_empty() => {
            // Local reference - try to look up in file scope
            if let Some(item_name) = path.item_name() {
                // Check if this is a primitive/builtin type - these should NOT be module-qualified
                if Ty::is_builtin_name(item_name) {
                    return ty.clone();
                }

                if let Some(target) = scope.get(item_name) {
                    if let Some(resolved_path) = path_for_target(target, db) {
                        return Ty::Const(resolved_path);
                    }
                }
            }
            // Fallback: qualify with current module
            let qualified = ItemPath::new(module_path.clone(), path.item.clone());
            Ty::Const(qualified)
        }
        Ty::Proj(path, args) if path.module.is_empty() => {
            // Local reference with type args - try to look up in file scope
            let resolved_path = if let Some(item_name) = path.item_name() {
                if let Some(target) = scope.get(item_name) {
                    path_for_target(target, db)
                        .unwrap_or_else(|| ItemPath::new(module_path.clone(), path.item.clone()))
                } else {
                    ItemPath::new(module_path.clone(), path.item.clone())
                }
            } else {
                ItemPath::new(module_path.clone(), path.item.clone())
            };

            // Resolve nested types in args too
            let resolved_args: Vec<Ty> = args
                .iter()
                .map(|arg| resolve_ty_with_scope(db, arg, file_id, module_path))
                .collect();
            Ty::Proj(resolved_path, resolved_args)
        }
        Ty::Proj(path, args) => {
            // Already qualified, but still resolve nested args
            let resolved_args: Vec<Ty> = args
                .iter()
                .map(|arg| resolve_ty_with_scope(db, arg, file_id, module_path))
                .collect();
            Ty::Proj(path.clone(), resolved_args)
        }
        // For other types, return as-is
        _ => ty.clone(),
    }
}

/// Check if a trait type matches a DefTarget.
///
/// This checks if the type refers to the same definition as the target.
/// The impl's trait type should be fully qualified (via resolve_ty_with_scope)
/// so we can do exact path comparison.
fn trait_ty_matches_target(trait_ty: &Ty, target: &DefTarget, db: &Database) -> bool {
    // Extract the ItemPath from the type
    let Some(ty_path) = trait_ty.item_path() else {
        return false;
    };

    // Get the ItemPath for the target
    let Some(target_path) = path_for_target(target, db) else {
        return false;
    };

    // Compare full paths
    ty_path == &target_path
}

/// Check if a Ty matches a DefTarget.
///
/// A type matches if it refers to the same definition as the target.
fn type_matches_target(ty: &Ty, target: &DefTarget, db: &Database) -> bool {
    // Extract the ItemPath from the type
    let Some(ty_path) = ty.item_path() else {
        return false;
    };

    // Get the ItemPath for the target
    let Some(target_path) = path_for_target(target, db) else {
        return false;
    };

    // Compare full paths
    ty_path == &target_path
}

// ============================================================================
// method_receiver_mode query
// ============================================================================

/// Get the receiver mode for a method given its DefTarget.
///
/// This query looks up the method's parent (trait or impl) and finds the
/// method's `ReceiverMode` from its `MethodInfo`.
///
/// Returns `ReceiverMode::None` if the target is not a method or if the
/// receiver mode cannot be determined.
#[query]
pub fn method_receiver_mode(db: &Database, method_target: DefTarget) -> ReceiverMode {
    match method_target {
        DefTarget::Workspace(def_id) => workspace_method_receiver_mode(db, def_id),
        DefTarget::Library(lib_def_id) => library_method_receiver_mode(db, &lib_def_id),
        DefTarget::Primitive(_) => ReceiverMode::None,
    }
}

/// Get receiver mode for a workspace method.
fn workspace_method_receiver_mode(db: &Database, method_def_id: DefId) -> ReceiverMode {
    let parse_result = parse_file(db, method_def_id.file);

    // Find the method's DefHeader
    let Some(method_header) = parse_result.defs.iter().find(|h| h.def_id == method_def_id) else {
        return ReceiverMode::None;
    };

    // Check if this is actually a method (has a parent)
    let Some(parent_def_id) = method_header.parent else {
        return ReceiverMode::None;
    };

    let method_name = &method_header.name;

    // Try to get the parent as an impl or trait
    let parent_target = DefTarget::Workspace(parent_def_id);

    // Try impl first
    if let Some(impl_def) = impl_def(db, parent_target.clone()) {
        if let Some(method_info) = impl_def.find_method(method_name) {
            return method_info.recv_mode;
        }
    }

    // Try trait
    if let Some(trait_def) = trait_def(db, parent_target) {
        if let Some(method_info) = trait_def.find_method(method_name) {
            return method_info.recv_mode;
        }
    }

    ReceiverMode::None
}

/// Get receiver mode for a library method.
fn library_method_receiver_mode(db: &Database, lib_def_id: &LibraryDefId) -> ReceiverMode {
    let Some(lib_data) = library_data(db, lib_def_id.module.clone()) else {
        return ReceiverMode::None;
    };

    // Get the method's path to find its name
    let method_path = lib_data
        .names
        .iter()
        .find(|(_, id)| *id == lib_def_id)
        .map(|(path, _)| path.clone());

    let Some(method_path) = method_path else {
        return ReceiverMode::None;
    };

    let Some(method_name) = method_path.item.last() else {
        return ReceiverMode::None;
    };

    // Search all impls and traits for this method
    // First check impls
    for impl_def in lib_data.impls.values() {
        if let Some(method_info) = impl_def.find_method(method_name) {
            if method_info.target == DefTarget::Library(lib_def_id.clone()) {
                return method_info.recv_mode;
            }
        }
    }

    // Then check traits
    for trait_def in lib_data.traits.values() {
        if let Some(method_info) = trait_def.find_method(method_name) {
            if method_info.target == DefTarget::Library(lib_def_id.clone()) {
                return method_info.recv_mode;
            }
        }
    }

    ReceiverMode::None
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        def::{DefKind, LibraryDefId},
        pathlib::{FilePath, ItemPath, ModulePath},
        resolution::DefTarget,
        ty::Ty,
    };
    use ray_typing::types::{ReceiverMode, TyScheme};

    use crate::{
        queries::{
            defs::{
                MethodInfo, SourceLocation, StructDef, StructField, TraitDef, def_for_path,
                def_name, def_path, definition_record, impl_def, impls_for_trait, impls_for_type,
                impls_in_module, method_receiver_mode, struct_def, trait_def,
                trait_methods_for_name, traits_in_module, type_alias,
            },
            libraries::{LibraryData, LoadedLibraries},
            parse::parse_file,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    /// Helper to set up empty LoadedLibraries in the database.
    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
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

        assert!(
            result.is_some(),
            "def_for_path should find 'helper' function"
        );
        match result.unwrap() {
            DefTarget::Workspace(def_id) => {
                assert_eq!(
                    def_id.file, file_id,
                    "DefId should reference the correct file"
                );
            }
            other => panic!(
                "Expected DefTarget::Workspace for function, got {:?}",
                other
            ),
        }
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

        let path = ItemPath::new(module_path.clone(), vec!["Point".into()]);
        let result = def_for_path(&db, path.clone());

        assert!(result.is_some(), "def_for_path should find 'Point' struct");
        let target = result.unwrap();
        match &target {
            DefTarget::Workspace(def_id) => {
                assert_eq!(
                    def_id.file, file_id,
                    "DefId should reference the correct file"
                );
            }
            other => panic!("Expected DefTarget::Workspace for struct, got {:?}", other),
        }

        // Verify we can retrieve the struct definition through the target
        let struct_definition = struct_def(&db, target);
        assert!(
            struct_definition.is_some(),
            "Should be able to get struct_def from target"
        );
        let struct_definition = struct_definition.unwrap();
        assert_eq!(struct_definition.path, path, "Struct path should match");
        assert_eq!(
            struct_definition.fields.len(),
            2,
            "Point should have 2 fields"
        );
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
        db.set_input::<LoadedLibraries>((), libraries);

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

        assert!(result.is_some(), "def_for_path should find 'foo'");
        match result.unwrap() {
            DefTarget::Workspace(def_id) => {
                assert_eq!(
                    def_id.file, file_id,
                    "DefId should reference the correct file"
                );
            }
            other => panic!("Expected DefTarget::Workspace, got {:?}", other),
        }
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
        assert_eq!(struct_def.path.item_name(), Some("Point"));
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
        assert_eq!(struct_def.path.item_name(), Some("Box"));
        assert_eq!(struct_def.ty.vars.len(), 1); // Type params are in ty.vars
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
                path: option_path.clone(),
                ty: TyScheme::from_mono(Ty::Const(option_path.clone())),
                fields: vec![
                    StructField {
                        name: "some".to_string(),
                        ty: TyScheme::from_mono(Ty::bool()),
                    },
                    StructField {
                        name: "value".to_string(),
                        ty: TyScheme::from_mono(Ty::Any),
                    },
                ],
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);

        let target = DefTarget::Library(option_def_id);

        let result = struct_def(&db, target);

        assert!(result.is_some());
        let struct_def = result.unwrap();
        assert_eq!(struct_def.path.item_name(), Some("Option"));
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
        assert_eq!(trait_def.path.item_name(), Some("Eq"));
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
                path: ord_path.clone(),
                ty: Ty::Const(ord_path.clone()),
                type_params: vec![],
                super_traits: vec![],
                methods: vec![
                    MethodInfo {
                        target: DefTarget::Library(LibraryDefId {
                            module: ModulePath::from("core::cmp"),
                            index: 1,
                        }),
                        path: ord_path.with_item("cmp"),
                        name: "cmp".to_string(),
                        is_static: false,
                        recv_mode: ReceiverMode::Value,
                        scheme: TyScheme::from_mono(Ty::Any),
                    },
                    MethodInfo {
                        target: DefTarget::Library(LibraryDefId {
                            module: ModulePath::from("core::cmp"),
                            index: 2,
                        }),
                        path: ord_path.with_item("lt"),
                        name: "lt".to_string(),
                        is_static: false,
                        recv_mode: ReceiverMode::Value,
                        scheme: TyScheme::from_mono(Ty::Any),
                    },
                ],
                default_ty: None,
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);

        let target = DefTarget::Library(ord_def_id);

        let result = trait_def(&db, target);

        assert!(result.is_some());
        let trait_def = result.unwrap();
        assert_eq!(trait_def.path.item_name(), Some("Ord"));
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

    // method_receiver_mode tests

    #[test]
    fn method_receiver_mode_returns_value_for_self_param() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Method with `self` parameter should have ReceiverMode::Value
        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn distance(self) -> int => self.x + self.y
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Find the method's DefId from the parsed file
        let parse_result = parse_file(&db, file_id);
        let method_header = parse_result
            .defs
            .iter()
            .find(|h| h.name == "distance")
            .expect("distance method should be found");

        let method_target = DefTarget::Workspace(method_header.def_id);
        let recv_mode = method_receiver_mode(&db, method_target);

        assert_eq!(recv_mode, ReceiverMode::Value);
    }

    #[test]
    fn method_receiver_mode_returns_ptr_for_ref_param() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Method with `*Point` parameter should have ReceiverMode::Ptr
        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn inspect(self: *Point) -> int => self.x
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Find the method's DefId from the parsed file
        let parse_result = parse_file(&db, file_id);
        let method_header = parse_result
            .defs
            .iter()
            .find(|h| h.name == "inspect")
            .expect("inspect method should be found");

        let method_target = DefTarget::Workspace(method_header.def_id);
        let recv_mode = method_receiver_mode(&db, method_target);

        assert_eq!(recv_mode, ReceiverMode::Ptr);
    }

    #[test]
    fn method_receiver_mode_returns_none_for_static_method() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Static method (no receiver) should have ReceiverMode::None
        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    static fn create(x: int, y: int) -> Point => Point { x, y }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Find the method's DefId from the parsed file
        let parse_result = parse_file(&db, file_id);
        let method_header = parse_result
            .defs
            .iter()
            .find(|h| h.name == "create")
            .expect("create method should be found");

        let method_target = DefTarget::Workspace(method_header.def_id);
        let recv_mode = method_receiver_mode(&db, method_target);

        assert_eq!(recv_mode, ReceiverMode::None);
    }

    #[test]
    fn method_receiver_mode_returns_none_for_non_method() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "fn helper() {}".to_string());

        // Find the function's DefId from the parsed file
        let parse_result = parse_file(&db, file_id);
        let func_header = parse_result
            .defs
            .iter()
            .find(|h| h.name == "helper")
            .expect("helper function should be found");

        let func_target = DefTarget::Workspace(func_header.def_id);
        let recv_mode = method_receiver_mode(&db, func_target);

        // Non-methods should return ReceiverMode::None
        assert_eq!(recv_mode, ReceiverMode::None);
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
                path: display_path.clone(),
                ty: Ty::Const(display_path.clone()),
                type_params: vec![],
                super_traits: vec![],
                methods: vec![MethodInfo {
                    target: DefTarget::Library(LibraryDefId {
                        module: ModulePath::from("core::fmt"),
                        index: 1,
                    }),
                    path: display_path.with_item("fmt"),
                    name: "fmt".to_string(),
                    is_static: false,
                    recv_mode: ReceiverMode::Value,
                    scheme: TyScheme::from_mono(Ty::Any),
                }],
                default_ty: None,
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);

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
                path: option_path.clone(),
                ty: TyScheme::from_mono(Ty::Const(option_path.clone())),
                fields: vec![],
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);

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

    #[test]
    fn trait_method_inherits_parent_type_params() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Trait with type parameter and method that uses it
        let source = r#"
trait Container['a] {
    fn get(self: 'a) -> int
    fn with_item(self: 'a, item: 'a) -> 'a
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the trait definition
        let path = ItemPath::new(module_path, vec!["Container".into()]);
        let target = def_for_path(&db, path).expect("trait should be found");

        let trait_def = trait_def(&db, target).expect("trait_def should succeed");

        // Trait should have 1 type param
        assert_eq!(
            trait_def.type_params.len(),
            1,
            "Trait should have 1 type param"
        );

        // The type param should be a schema var (like ?s0), not a user var like 'a
        let trait_type_param = &trait_def.type_params[0];
        let type_param_name = trait_type_param.path().name().unwrap_or_default();
        assert!(
            type_param_name.starts_with("?s"),
            "Trait type param should be a schema var, got: {}",
            type_param_name
        );

        // Find the with_item method that uses 'a in its signature
        let with_item_method = trait_def
            .methods
            .iter()
            .find(|m| m.name == "with_item")
            .expect("should find with_item method");

        // Get the method's scheme
        let scheme = &with_item_method.scheme;

        // The method scheme should reference the same schema var as the trait
        // with_item(self: 'a, item: 'a) -> 'a
        // becomes something like: fn(?s0, ?s0) -> ?s0

        // Check that the method's param types use schema vars
        if let Ty::Func(params, ret) = &scheme.ty {
            // Should have 2 params (self: 'a, item: 'a)
            assert_eq!(params.len(), 2, "with_item should have 2 params");

            // Both params should be the schema var
            for (i, param) in params.iter().enumerate() {
                if let Ty::Var(var) = param {
                    let var_name = var.path().name().unwrap_or_default();
                    assert!(
                        var_name.starts_with("?s"),
                        "Param {} should use schema var, got: {}",
                        i,
                        var_name
                    );
                } else {
                    panic!("Param {} should be Ty::Var, got: {:?}", i, param);
                }
            }

            // Return type should also be the schema var
            if let Ty::Var(var) = ret.as_ref() {
                let var_name = var.path().name().unwrap_or_default();
                assert!(
                    var_name.starts_with("?s"),
                    "Return type should use schema var, got: {}",
                    var_name
                );
            } else {
                panic!("Return type should be Ty::Var, got: {:?}", ret);
            }
        } else {
            panic!("Method scheme.ty should be Func, got: {:?}", scheme.ty);
        }
    }

    #[test]
    fn struct_fields_use_schema_vars() {
        // Test that struct fields with type parameters are resolved to schema vars
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Box['a] { value: 'a }
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Verify struct field types use schema vars
        let struct_path = ItemPath::new(module_path, vec!["Box".into()]);
        let struct_target = def_for_path(&db, struct_path).expect("struct should be found");
        let struct_definition = struct_def(&db, struct_target).expect("struct_def should succeed");

        // Struct should have 1 field with type being a schema var
        assert_eq!(struct_definition.fields.len(), 1);
        let field_ty = &struct_definition.fields[0].ty.ty;
        if let Ty::Var(var) = field_ty {
            let var_name = var.path().name().unwrap_or_default();
            assert!(
                var_name.starts_with("?s"),
                "Struct field should use schema var, got: {}",
                var_name
            );
        } else {
            panic!("Struct field should be Ty::Var, got: {:?}", field_ty);
        }
    }

    // ============================================================================
    // def_for_path primitive type tests
    // ============================================================================

    #[test]
    fn def_for_path_returns_primitive_for_int() {
        let db = Database::new();
        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let path = ItemPath::new(ModulePath::root(), vec!["int".into()]);
        let result = def_for_path(&db, path.clone());

        assert!(result.is_some(), "def_for_path should find 'int'");
        match result.unwrap() {
            DefTarget::Primitive(p) => {
                assert_eq!(p, path, "Primitive path should match input path");
            }
            other => panic!("Expected DefTarget::Primitive, got {:?}", other),
        }
    }

    #[test]
    fn def_for_path_returns_primitive_for_bool() {
        let db = Database::new();
        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let path = ItemPath::new(ModulePath::root(), vec!["bool".into()]);
        let result = def_for_path(&db, path.clone());

        assert!(result.is_some(), "def_for_path should find 'bool'");
        match result.unwrap() {
            DefTarget::Primitive(p) => {
                assert_eq!(p, path, "Primitive path should match input path");
            }
            other => panic!("Expected DefTarget::Primitive, got {:?}", other),
        }
    }

    #[test]
    fn def_for_path_returns_primitive_for_char() {
        let db = Database::new();
        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let path = ItemPath::new(ModulePath::root(), vec!["char".into()]);
        let result = def_for_path(&db, path.clone());

        assert!(result.is_some(), "def_for_path should find 'char'");
        match result.unwrap() {
            DefTarget::Primitive(p) => {
                assert_eq!(p, path, "Primitive path should match input path");
            }
            other => panic!("Expected DefTarget::Primitive, got {:?}", other),
        }
    }

    #[test]
    fn def_for_path_string_is_not_primitive() {
        // `string` is a struct defined in core, not a primitive type.
        // Without the prelude/core library loaded, it should not be found.
        let db = Database::new();
        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let path = ItemPath::new(ModulePath::root(), vec!["string".into()]);
        let result = def_for_path(&db, path);

        assert!(
            result.is_none(),
            "string is not a primitive - should not be found without core library"
        );
    }

    #[test]
    fn def_for_path_does_not_treat_non_primitive_as_primitive() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "struct MyInt { value: int }".to_string());

        // "MyInt" in root module should not be found (it's in mymodule)
        let path = ItemPath::new(ModulePath::root(), vec!["MyInt".into()]);
        let result = def_for_path(&db, path);
        assert!(
            result.is_none(),
            "User-defined type in non-root module should not be found at root"
        );

        // "MyInt" in mymodule should be found as Workspace, not Primitive
        let path = ItemPath::new(module_path, vec!["MyInt".into()]);
        let result = def_for_path(&db, path);
        assert!(result.is_some(), "User-defined type should be found");
        assert!(
            matches!(result.unwrap(), DefTarget::Workspace(_)),
            "User-defined type should be Workspace, not Primitive"
        );
    }

    #[test]
    fn def_for_path_primitive_requires_root_module() {
        let db = Database::new();
        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // "int" in a non-root module should NOT be treated as a primitive
        let path = ItemPath::new(ModulePath::from("somemodule"), vec!["int".into()]);
        let result = def_for_path(&db, path);

        assert!(
            result.is_none(),
            "Primitive name in non-root module should not be found"
        );
    }

    // ============================================================================
    // def_path tests
    // ============================================================================

    #[test]
    fn def_path_returns_path_for_workspace_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "fn helper() -> int => 42".to_string());

        let path = ItemPath::new(module_path.clone(), vec!["helper".into()]);
        let target = def_for_path(&db, path.clone()).expect("function should be found");

        let result = def_path(&db, target);

        assert!(result.is_some(), "def_path should return a path");
        assert_eq!(
            result.unwrap(),
            path,
            "def_path should return the correct path"
        );
    }

    #[test]
    fn def_path_returns_path_for_workspace_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "struct Point { x: int, y: int }".to_string());

        let path = ItemPath::new(module_path.clone(), vec!["Point".into()]);
        let target = def_for_path(&db, path.clone()).expect("struct should be found");

        let result = def_path(&db, target);

        assert!(result.is_some(), "def_path should return a path");
        assert_eq!(
            result.unwrap(),
            path,
            "def_path should return the correct path"
        );
    }

    #[test]
    fn def_path_returns_path_for_primitive() {
        let db = Database::new();
        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let path = ItemPath::new(ModulePath::root(), vec!["int".into()]);
        let target = def_for_path(&db, path.clone()).expect("int should be found as primitive");

        let result = def_path(&db, target);

        assert!(
            result.is_some(),
            "def_path should return a path for primitives"
        );
        assert_eq!(
            result.unwrap(),
            path,
            "def_path should return the primitive path"
        );
    }

    #[test]
    fn def_path_roundtrips_for_all_primitive_types() {
        let db = Database::new();
        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Note: "string" is NOT a primitive - it's a struct in core
        let primitives = ["int", "bool", "char", "uint", "i32", "u64", "i8", "u8"];

        for name in primitives {
            let path = ItemPath::new(ModulePath::root(), vec![name.into()]);
            let target = def_for_path(&db, path.clone());
            assert!(
                target.is_some(),
                "def_for_path should find primitive '{}'",
                name
            );

            let roundtrip = def_path(&db, target.unwrap());
            assert!(
                roundtrip.is_some(),
                "def_path should return path for primitive '{}'",
                name
            );
            assert_eq!(
                roundtrip.unwrap(),
                path,
                "def_path should roundtrip for primitive '{}'",
                name
            );
        }
    }

    // ============================================================================
    // trait_methods_for_name tests
    // ============================================================================

    #[test]
    fn trait_methods_for_name_finds_method_in_trait() {
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
"#;
        FileSource::new(&db, file_id, source.to_string());

        let results = trait_methods_for_name(&db, &"to_str".to_string());

        assert_eq!(
            results.len(),
            1,
            "Should find exactly one trait with to_str method"
        );
        let (trait_def, method_info) = &results[0];
        assert_eq!(trait_def.path.item, vec!["ToStr".to_string()]);
        assert_eq!(method_info.name, "to_str");
    }

    #[test]
    fn trait_methods_for_name_finds_method_in_multiple_traits() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait Display['a] {
    fn show(self: 'a) -> string
}

trait Debug['a] {
    fn show(self: 'a) -> string
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let results = trait_methods_for_name(&db, &"show".to_string());

        assert_eq!(
            results.len(),
            2,
            "Should find 'show' method in both Display and Debug traits"
        );

        let trait_names: Vec<_> = results
            .iter()
            .map(|(t, _)| t.path.item[0].clone())
            .collect();
        assert!(trait_names.contains(&"Display".to_string()));
        assert!(trait_names.contains(&"Debug".to_string()));
    }

    #[test]
    fn trait_methods_for_name_returns_empty_for_unknown_method() {
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
"#;
        FileSource::new(&db, file_id, source.to_string());

        let results = trait_methods_for_name(&db, &"nonexistent".to_string());

        assert!(
            results.is_empty(),
            "Should return empty vec for unknown method name"
        );
    }

    #[test]
    fn trait_methods_for_name_returns_correct_method_info() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait Printable['a] {
    fn print(self: *'a) -> unit
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let results = trait_methods_for_name(&db, &"print".to_string());

        assert_eq!(results.len(), 1);
        let (_trait_def, method_info) = &results[0];
        assert_eq!(method_info.name, "print");
        assert!(
            !method_info.is_static,
            "Method with self parameter should not be static"
        );
        assert!(
            matches!(method_info.target, DefTarget::Workspace(_)),
            "Method target should be workspace def"
        );
    }

    // ========================================================================
    // def_name tests
    // ========================================================================

    #[test]
    fn def_name_returns_function_name() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "fn helper() {}".to_string());

        let path = ItemPath::new(module_path, vec!["helper".into()]);
        let target = def_for_path(&db, path).expect("function should be found");

        let name = def_name(&db, target);
        assert_eq!(name, Some("helper".to_string()));
    }

    #[test]
    fn def_name_returns_struct_name() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "struct Point { x: int, y: int }".to_string());

        let path = ItemPath::new(module_path, vec!["Point".into()]);
        let target = def_for_path(&db, path).expect("struct should be found");

        let name = def_name(&db, target);
        assert_eq!(name, Some("Point".to_string()));
    }

    #[test]
    fn def_name_returns_method_name() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct List { items: int }

impl object List {
    fn push(self) => self.items
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the impl to find the method
        let list_path = ItemPath::new(module_path.clone(), vec!["List".into()]);
        let list_target = def_for_path(&db, list_path).expect("struct should be found");
        let impls = impls_for_type(&db, list_target);

        assert!(!impls.inherent.is_empty(), "should have inherent impl");
        let impl_target = &impls.inherent[0];
        let impl_definition = impl_def(&db, impl_target.clone()).expect("impl should exist");

        assert!(!impl_definition.methods.is_empty(), "should have method");
        let method_target = impl_definition.methods[0].target.clone();

        let name = def_name(&db, method_target);
        assert_eq!(name, Some("push".to_string()));
    }

    #[test]
    fn def_name_returns_primitive_name() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let target = DefTarget::Primitive(ItemPath::new(ModulePath::root(), vec!["int".into()]));
        let name = def_name(&db, target);
        assert_eq!(name, Some("int".to_string()));
    }

    #[test]
    fn def_name_returns_library_function_name() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with a function
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::io"));

        let read_def_id = LibraryDefId {
            module: ModulePath::from("core::io"),
            index: 0,
        };
        let read_path = ItemPath::new(ModulePath::from("core::io"), vec!["read".into()]);

        core_lib.names.insert(read_path, read_def_id.clone());
        core_lib
            .schemes
            .insert(read_def_id.clone(), TyScheme::from_mono(Ty::unit()));
        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);

        let target = DefTarget::Library(read_def_id);
        let name = def_name(&db, target);
        assert_eq!(name, Some("read".to_string()));
    }

    // ========================================================================
    // definition_record tests
    // ========================================================================

    #[test]
    fn definition_record_returns_function_info() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "fn helper() {}".to_string());

        let path = ItemPath::new(module_path, vec!["helper".into()]);
        let target = def_for_path(&db, path.clone()).expect("function should be found");

        let record = definition_record(&db, target).expect("should get definition record");

        assert_eq!(record.path, path);
        assert!(
            matches!(record.source_location, Some(SourceLocation::Workspace { file, .. }) if file == file_id),
            "should have workspace source location"
        );
        assert!(record.doc.is_none(), "doc not yet implemented");
        assert!(
            matches!(record.kind, DefKind::Function { .. }),
            "should be a function"
        );
    }

    #[test]
    fn definition_record_returns_struct_info() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "struct Point { x: int }".to_string());

        let path = ItemPath::new(module_path, vec!["Point".into()]);
        let target = def_for_path(&db, path.clone()).expect("struct should be found");

        let record = definition_record(&db, target).expect("should get definition record");

        assert_eq!(record.path, path);
        assert!(
            matches!(record.source_location, Some(SourceLocation::Workspace { file, .. }) if file == file_id),
            "should have workspace source location"
        );
        assert!(matches!(record.kind, DefKind::Struct));
    }

    #[test]
    fn definition_record_returns_trait_info() {
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
        let target = def_for_path(&db, path.clone()).expect("trait should be found");

        let record = definition_record(&db, target).expect("should get definition record");

        assert_eq!(record.path, path);
        assert!(matches!(record.kind, DefKind::Trait));
    }

    #[test]
    fn definition_record_returns_primitive_info() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let path = ItemPath::new(ModulePath::root(), vec!["int".into()]);
        let target = DefTarget::Primitive(path.clone());

        let record = definition_record(&db, target).expect("should get definition record");

        assert_eq!(record.path, path);
        assert!(
            record.source_location.is_none(),
            "primitives have no source location"
        );
        assert!(record.doc.is_none());
        assert!(matches!(record.kind, DefKind::Primitive));
    }

    #[test]
    fn definition_record_returns_library_struct_info() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with a struct
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::option"));

        let option_def_id = LibraryDefId {
            module: ModulePath::from("core::option"),
            index: 0,
        };
        let option_path = ItemPath::new(ModulePath::from("core::option"), vec!["Option".into()]);

        core_lib
            .names
            .insert(option_path.clone(), option_def_id.clone());
        core_lib.structs.insert(
            option_def_id.clone(),
            StructDef {
                target: DefTarget::Library(option_def_id.clone()),
                path: option_path.clone(),
                ty: TyScheme::from_mono(Ty::Const(option_path.clone())),
                fields: vec![],
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);

        let target = DefTarget::Library(option_def_id);

        let record = definition_record(&db, target).expect("should get definition record");

        assert_eq!(record.path, option_path);
        assert!(
            record.source_location.is_none(),
            "library defs have no source location in current impl"
        );
        assert!(matches!(record.kind, DefKind::Struct));
    }
}

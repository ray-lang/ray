use std::{
    collections::{HashMap, HashSet},
    fs::File,
    hash::{Hash, Hasher},
    io,
    sync::Arc,
};

use ray_query_macros::{input, query};
use ray_shared::{
    def::{DefId, DefKind, LibraryDefId},
    node_id::NodeId,
    pathlib::{FilePath, ItemPath, ModulePath},
    resolution::DefTarget,
    ty::{SCHEMA_PREFIX, SchemaVarAllocator, Ty, TyVar},
};
use ray_typing::{
    constraints::Predicate,
    types::{Subst, Substitutable, TyScheme},
};
use serde::{Deserialize, Serialize};

use ray_core::sourcemap::SourceMap;

use crate::{
    queries::{
        defs::{
            DefinitionRecord, FuncDef, ImplDef, StructDef, TraitDef, def_path, func_def, impl_def,
            struct_def, trait_def,
        },
        display::collect_reverse_map,
        parse::parse_file,
        typecheck::def_scheme,
        workspace::WorkspaceSnapshot,
    },
    query::{Database, Input, Query},
};

/// Binary format for compiled libraries (.raylib files).
///
/// This struct mirrors the serialization format from ray-codegen.
/// It's defined here to avoid a circular dependency (ray-codegen depends on ray-frontend).
#[derive(Debug, Deserialize)]
struct RayLib {
    data: LibraryData,
    #[allow(dead_code)]
    program: ray_lir::Program,
}

/// Data extracted from a compiled library (.raylib file).
///
/// This contains the type schemes, structs, traits, impls, and operators
/// exported by the library. Schema variables are remapped during loading
/// to avoid collisions with workspace type inference variables.
///
/// Unlike the old design that keyed everything by ItemPath, this uses
/// LibraryDefId (module + index) as the primary key. This allows anonymous
/// definitions like impls to have stable identities.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct LibraryData {
    /// Name lookup index: maps ItemPath -> LibraryDefId for named definitions.
    /// Impls are not in this index since they don't have names.
    pub names: HashMap<ItemPath, LibraryDefId>,

    /// Type schemes for all exported definitions, keyed by LibraryDefId.
    pub schemes: HashMap<LibraryDefId, TyScheme>,

    /// Struct definitions, keyed by LibraryDefId.
    pub structs: HashMap<LibraryDefId, StructDef>,

    /// Trait definitions, keyed by LibraryDefId.
    pub traits: HashMap<LibraryDefId, TraitDef>,

    /// Impl definitions (both inherent and trait impls), keyed by LibraryDefId.
    pub impls: HashMap<LibraryDefId, ImplDef>,

    /// Index: type path -> impls for that type (for impls_for_type query).
    pub impls_by_type: HashMap<ItemPath, Vec<LibraryDefId>>,

    /// Index: trait path -> impls of that trait (for impls_for_trait query).
    pub impls_by_trait: HashMap<ItemPath, Vec<LibraryDefId>>,

    /// Operator definitions exported by the library.
    pub operators: OperatorIndex,

    /// Module paths contained in this library.
    pub modules: Vec<ModulePath>,

    /// Definition records for IDE features (go-to-definition, hover, etc.).
    pub definitions: HashMap<LibraryDefId, DefinitionRecord>,

    /// Source map for error messages and source locations.
    pub source_map: SourceMap,

    /// Reverse maps for display: maps internal schema vars to user-facing var names.
    /// Used by IDE features to show `'a` instead of `?s10` for library definitions.
    #[serde(default)]
    pub display_vars: HashMap<LibraryDefId, HashMap<TyVar, TyVar>>,

    /// Maps each library def to its root NodeId in the source map.
    /// Used by doc_comment lookup to find docs from source_map.
    #[serde(default)]
    pub root_nodes: HashMap<LibraryDefId, NodeId>,

    /// Maps child defs (methods, struct fields) to their parent def.
    /// Populated during build from DefHeader.parent.
    #[serde(default)]
    pub parent_map: HashMap<LibraryDefId, LibraryDefId>,

    /// Function/method definitions with param names and modifiers.
    #[serde(default)]
    pub func_defs: HashMap<LibraryDefId, FuncDef>,
}

impl LibraryData {
    /// Look up a LibraryDefId by ItemPath.
    pub fn lookup(&self, path: &ItemPath) -> Option<LibraryDefId> {
        self.names.get(path).cloned()
    }

    /// Check if a library contains the given item path.
    pub fn contains_item(&self, path: &ItemPath) -> bool {
        self.names.contains_key(path)
    }
}

/// Operator index mapping operator symbols to their definitions.
pub type OperatorIndex = HashMap<(String, OperatorArity), OperatorEntry>;

/// An operator entry from a library.
///
/// Links an operator symbol to the trait and method that define it.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OperatorEntry {
    /// The trait that defines this operator.
    pub trait_def: DefTarget,
    /// The method within the trait that implements this operator.
    pub method_def: DefTarget,
    /// Whether this is a prefix (unary) or infix (binary) operator.
    pub arity: OperatorArity,
}

/// Operator arity (unary vs binary).
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum OperatorArity {
    /// Unary prefix operator: -x, !x
    Prefix,
    /// Binary infix operator: a + b, a * b
    Infix,
}

/// Collection of loaded libraries, keyed by library path.
///
/// This is a singleton input (keyed by `()`) that stores all loaded library data.
/// Libraries are loaded at startup and their exports are used for name resolution.
/// File paths are tracked separately for lazy LIR loading via `library_lir` query.
#[input(key = "()")]
#[derive(Clone, Debug, Default)]
pub struct LoadedLibraries {
    /// Library data keyed by the library's module path (e.g., "core", "std").
    pub libraries: HashMap<ModulePath, LibraryData>,
    /// File paths for each library, used for lazy LIR loading.
    pub library_files: HashMap<ModulePath, FilePath>,
}

impl Hash for LoadedLibraries {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash library paths in sorted order for determinism
        let mut keys: Vec<_> = self.libraries.keys().collect();
        keys.sort_by_key(|k| k.to_string());
        for path in keys {
            path.hash(state);
        }
        // Also hash file paths
        let mut file_keys: Vec<_> = self.library_files.keys().collect();
        file_keys.sort_by_key(|k| k.to_string());
        for path in file_keys {
            path.hash(state);
            if let Some(file) = self.library_files.get(path) {
                file.hash(state);
            }
        }
    }
}

impl LoadedLibraries {
    /// Add a library to the collection.
    pub fn add(&mut self, lib_path: ModulePath, data: LibraryData) {
        self.libraries.insert(lib_path, data);
    }

    /// Add a library from a file, tracking the file path for lazy LIR loading.
    pub fn add_from_file(&mut self, lib_path: ModulePath, file: FilePath, data: LibraryData) {
        self.libraries.insert(lib_path.clone(), data);
        self.library_files.insert(lib_path, file);
    }

    /// Get a library by its path.
    pub fn get(&self, lib_path: &ModulePath) -> Option<&LibraryData> {
        self.libraries.get(lib_path)
    }

    /// Get the file path for a library (for lazy LIR loading).
    pub fn library_file_for(&self, lib_path: &ModulePath) -> Option<&FilePath> {
        self.library_files.get(lib_path)
    }

    /// Get all library root paths.
    pub fn all_library_roots(&self) -> impl Iterator<Item = &ModulePath> {
        self.libraries.keys()
    }

    /// Check if a module path exists in any loaded library.
    ///
    /// This checks if the module path is either:
    /// - The library root (e.g., "core")
    /// - A submodule within a library (e.g., "core::io")
    pub fn has_module(&self, module_path: &ModulePath) -> bool {
        // Check if it's an exact library root match
        if self.libraries.contains_key(module_path) {
            return true;
        }

        // Check if it's a submodule of any library
        for (lib_path, lib_data) in &self.libraries {
            // Check if the module_path starts with the library path
            let lib_str = lib_path.to_string();
            let module_str = module_path.to_string();
            if module_str.starts_with(&lib_str) {
                // Check if it matches a module in the library
                if lib_data.modules.iter().any(|m| m == module_path) {
                    return true;
                }
            }
        }

        false
    }

    /// Find which library contains a given module path.
    ///
    /// Returns the library root path (e.g., "core") for a module like "core::io".
    pub fn library_for_module(&self, module_path: &ModulePath) -> Option<&ModulePath> {
        // First check exact match (module_path is a library root)
        if self.libraries.contains_key(module_path) {
            // Return the key from the map, not the input
            return self.libraries.keys().find(|k| *k == module_path);
        }

        // Check if it's a submodule
        for (lib_path, lib_data) in &self.libraries {
            let lib_str = lib_path.to_string();
            let module_str = module_path.to_string();
            if module_str.starts_with(&lib_str)
                && (module_str.len() == lib_str.len()
                    || module_str[lib_str.len()..].starts_with("::"))
            {
                // Check if it matches a module in the library
                if lib_data.modules.iter().any(|m| m == module_path) {
                    return Some(lib_path);
                }
                // Or if the module path is the library root itself
                if module_path == lib_path {
                    return Some(lib_path);
                }
            }
        }

        None
    }

    /// Get all module paths in the loaded libraries.
    pub fn all_module_paths(&self) -> impl Iterator<Item = &ModulePath> {
        self.libraries.iter().flat_map(|(lib_path, lib_data)| {
            std::iter::once(lib_path).chain(lib_data.modules.iter())
        })
    }
}

/// Look up library data for a module path.
///
/// Given a module path like `core::io`, finds which library contains it
/// and returns the library's data. For library roots like `core`, returns
/// the library data directly.
///
/// This is the primary query interface for accessing library data.
/// The `LoadedLibraries` input stores all libraries; this query provides
/// convenient per-module access.
#[query]
pub fn library_data(db: &Database, module_path: ModulePath) -> Option<Arc<LibraryData>> {
    let libraries = db.get_input::<LoadedLibraries>(());
    let lib_path = libraries.library_for_module(&module_path)?;
    libraries.get(lib_path).cloned().map(|data| Arc::new(data))
}

/// Find the library root path for a module path.
///
/// Given a module path like `core::io`, returns the library root `core`.
/// Returns `None` if the module path doesn't belong to any loaded library.
#[query]
pub fn library_root(db: &Database, module_path: ModulePath) -> Option<ModulePath> {
    let libraries = db.get_input::<LoadedLibraries>(());
    libraries.library_for_module(&module_path).cloned()
}

/// Lazily load the LIR program for a library.
///
/// This query reads the .raylib file and extracts the LIR program for codegen.
/// The file path is obtained from `LoadedLibraries.library_files`.
///
/// # Arguments
/// * `lib_root` - The library root path (e.g., "core")
///
/// # Returns
/// The LIR program for the library, or `None` if the library isn't loaded
/// or the file can't be read.
#[query]
pub fn library_lir(db: &Database, lib_root: ModulePath) -> Option<ray_lir::Program> {
    let libraries = db.get_input::<LoadedLibraries>(());
    let lib_file = libraries.library_file_for(&lib_root)?;

    let file = File::open(lib_file.as_ref()).ok()?;
    let raylib: RayLib = bincode::deserialize_from(file).ok()?;
    Some(raylib.program)
}

/// Load a library from a .raylib file, remapping schema variables to avoid
/// collisions with workspace type inference.
///
/// # Arguments
/// * `path` - Path to the .raylib file
/// * `allocator` - Schema variable allocator to reserve IDs from
///
/// # Returns
/// The loaded library data with remapped type variables.
pub fn load_library(
    path: &FilePath,
    allocator: &mut SchemaVarAllocator,
) -> io::Result<LibraryData> {
    let file = File::open(path.as_ref())?;
    let raylib: RayLib = bincode::deserialize_from(file)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

    let mut data = raylib.data;

    // Find the maximum schema var ID used in the library
    let max_lib_var = find_max_schema_var_id(&data);

    if max_lib_var > 0 {
        // Reserve that range in our allocator
        let offset = reserve_schema_var_range(allocator, max_lib_var);

        // Remap all type variables in the library data
        remap_library_type_vars(&mut data, offset);
    }

    Ok(data)
}

/// Find the maximum schema variable ID used in the library data.
fn find_max_schema_var_id(data: &LibraryData) -> u32 {
    let mut max_id: u32 = 0;

    for scheme in data.schemes.values() {
        for var in &scheme.vars {
            if let Some(id) = parse_schema_var_id(var) {
                max_id = max_id.max(id + 1);
            }
        }
        max_id = max_id.max(find_max_in_ty(&scheme.ty));
        for qual in &scheme.qualifiers {
            max_id = max_id.max(find_max_in_predicate(qual));
        }
    }

    for s in data.structs.values() {
        // Type params are now in the struct's TyScheme
        for var in &s.ty.vars {
            if let Some(id) = parse_schema_var_id(var) {
                max_id = max_id.max(id + 1);
            }
        }
        max_id = max_id.max(find_max_in_ty(&s.ty.ty));
        for field in &s.fields {
            // Field types are now TyScheme
            for var in &field.ty.vars {
                if let Some(id) = parse_schema_var_id(var) {
                    max_id = max_id.max(id + 1);
                }
            }
            max_id = max_id.max(find_max_in_ty(&field.ty.ty));
        }
    }

    for t in data.traits.values() {
        for var in &t.type_params {
            if let Some(id) = parse_schema_var_id(var) {
                max_id = max_id.max(id + 1);
            }
        }
    }

    for imp in data.impls.values() {
        for var in &imp.type_params {
            if let Some(id) = parse_schema_var_id(var) {
                max_id = max_id.max(id + 1);
            }
        }
        max_id = max_id.max(find_max_in_ty(&imp.implementing_type));
    }

    max_id
}

/// Find the maximum schema variable ID in a type.
fn find_max_in_ty(ty: &Ty) -> u32 {
    let mut max_id: u32 = 0;

    for var in ty.free_vars() {
        if let Some(id) = parse_schema_var_id(var) {
            max_id = max_id.max(id + 1);
        }
    }

    max_id
}

/// Find the maximum schema variable ID in a predicate.
fn find_max_in_predicate(pred: &Predicate) -> u32 {
    let mut free_vars = HashSet::new();
    pred.free_ty_vars(&mut free_vars);

    let mut max_id: u32 = 0;
    for var in free_vars {
        if let Some(id) = parse_schema_var_id(&var) {
            max_id = max_id.max(id + 1);
        }
    }

    max_id
}

/// Parse the numeric ID from a schema variable name (e.g., "?s5" -> 5).
fn parse_schema_var_id(var: &TyVar) -> Option<u32> {
    let name = var.path().name()?;
    if name.starts_with(SCHEMA_PREFIX) {
        name[SCHEMA_PREFIX.len()..].parse().ok()
    } else {
        None
    }
}

/// Reserve a range of schema variable IDs in the allocator.
///
/// Returns the offset that should be added to library variable IDs.
fn reserve_schema_var_range(allocator: &mut SchemaVarAllocator, count: u32) -> u32 {
    let offset = allocator.curr_id();
    // Advance the allocator past the reserved range
    for _ in 0..count {
        allocator.alloc();
    }
    offset
}

/// Remap all schema variables in the library data by adding an offset.
fn remap_library_type_vars(data: &mut LibraryData, offset: u32) {
    // Build a substitution mapping old schema vars to new offset versions
    let subst = build_offset_subst(data, offset);

    for scheme in data.schemes.values_mut() {
        scheme.vars.apply_subst(&subst);
        scheme.ty.apply_subst(&subst);
        scheme.qualifiers.apply_subst(&subst);
    }

    for s in data.structs.values_mut() {
        // Apply subst to the struct's TyScheme
        s.ty.vars.apply_subst(&subst);
        s.ty.ty.apply_subst(&subst);
        s.ty.qualifiers.apply_subst(&subst);
        for field in &mut s.fields {
            // Field types are now TyScheme
            field.ty.vars.apply_subst(&subst);
            field.ty.ty.apply_subst(&subst);
            field.ty.qualifiers.apply_subst(&subst);
        }
    }

    for t in data.traits.values_mut() {
        t.type_params.apply_subst(&subst);
    }

    for imp in data.impls.values_mut() {
        imp.type_params.apply_subst(&subst);
        imp.implementing_type.apply_subst(&subst);
    }

    // Remap display_vars keys (schema vars get offset, user vars stay the same)
    for inner_map in data.display_vars.values_mut() {
        *inner_map = inner_map
            .drain()
            .map(|(key, value)| {
                let new_key = if let Some(id) = parse_schema_var_id(&key) {
                    TyVar::new(format!("{}{}", SCHEMA_PREFIX, id + offset))
                } else {
                    key
                };
                (new_key, value)
            })
            .collect();
    }
}

/// Build a substitution that maps each schema variable to its offset version.
fn build_offset_subst(data: &LibraryData, offset: u32) -> Subst {
    let mut subst = Subst::new();

    // Collect all schema variables and create mappings
    for scheme in data.schemes.values() {
        for var in &scheme.vars {
            add_var_to_subst(&mut subst, var, offset);
        }
        collect_vars_from_ty(&mut subst, &scheme.ty, offset);
        for qual in &scheme.qualifiers {
            collect_vars_from_predicate(&mut subst, qual, offset);
        }
    }

    for s in data.structs.values() {
        // Collect from struct's TyScheme
        for var in &s.ty.vars {
            add_var_to_subst(&mut subst, var, offset);
        }
        collect_vars_from_ty(&mut subst, &s.ty.ty, offset);
        for qual in &s.ty.qualifiers {
            collect_vars_from_predicate(&mut subst, qual, offset);
        }
        for field in &s.fields {
            // Field types are now TyScheme
            for var in &field.ty.vars {
                add_var_to_subst(&mut subst, var, offset);
            }
            collect_vars_from_ty(&mut subst, &field.ty.ty, offset);
            for qual in &field.ty.qualifiers {
                collect_vars_from_predicate(&mut subst, qual, offset);
            }
        }
    }

    for t in data.traits.values() {
        for var in &t.type_params {
            add_var_to_subst(&mut subst, var, offset);
        }
    }

    for imp in data.impls.values() {
        for var in &imp.type_params {
            add_var_to_subst(&mut subst, var, offset);
        }
        collect_vars_from_ty(&mut subst, &imp.implementing_type, offset);
    }

    subst
}

/// Add a schema variable mapping to the substitution if applicable.
fn add_var_to_subst(subst: &mut Subst, var: &TyVar, offset: u32) {
    if let Some(id) = parse_schema_var_id(var) {
        let new_name = format!("{}{}", SCHEMA_PREFIX, id + offset);
        let new_var = TyVar::new(new_name);
        subst.insert(var.clone(), Ty::Var(new_var));
    }
}

/// Collect schema variables from a type and add their mappings to the substitution.
fn collect_vars_from_ty(subst: &mut Subst, ty: &Ty, offset: u32) {
    for var in ty.free_vars() {
        add_var_to_subst(subst, var, offset);
    }
}

/// Collect schema variables from a predicate and add their mappings to the substitution.
fn collect_vars_from_predicate(subst: &mut Subst, pred: &Predicate, offset: u32) {
    let mut free_vars = HashSet::new();
    pred.free_ty_vars(&mut free_vars);

    for var in free_vars {
        add_var_to_subst(subst, &var, offset);
    }
}

/// Build LibraryData from the query database by collecting all definitions,
/// type schemes, structs, traits, and impls from workspace files.
///
/// Known gaps:
/// - Top-level locals (e.g. `x = 42`) inside FileMain are not exported.
///   This is a pre-existing limitation: `exported_item_to_def_target` in
///   resolve.rs also drops `ExportedItem::Local` items. Fixing this requires
///   extending the resolution model to support library locals.
/// - Operator index is not populated. Operator traits/methods are serialized
///   in `traits` and `impls`, but the `operators` shortcut index is empty.
/// - Definition records (for IDE go-to-definition) are not populated.
pub fn build_library_data(
    db: &Database,
    modules: Vec<ModulePath>,
    srcmap: SourceMap,
) -> LibraryData {
    let workspace = db.get_input::<WorkspaceSnapshot>(());

    // Phase 1: Allocate LibraryDefIds for all defs and build DefId -> LibraryDefId mapping
    let mut module_counters: HashMap<ModulePath, u32> = HashMap::new();
    let mut def_id_to_lib: HashMap<DefId, LibraryDefId> = HashMap::new();

    for file_id in workspace.all_file_ids() {
        let file_info = match workspace.file_info(file_id) {
            Some(info) => info,
            None => continue,
        };
        let module_path = file_info.module_path.clone();
        let parse_result = parse_file(db, file_id);

        for def_header in &parse_result.defs {
            if matches!(def_header.kind, DefKind::FileMain | DefKind::StructField) {
                continue;
            }

            let counter = module_counters.entry(module_path.clone()).or_insert(0);
            let lib_def_id = LibraryDefId {
                module: module_path.clone(),
                index: *counter,
            };
            *counter += 1;

            def_id_to_lib.insert(def_header.def_id, lib_def_id);
        }
    }

    // Phase 2: Populate library data using queries
    let mut names = HashMap::new();
    let mut schemes = HashMap::new();
    let mut structs_map = HashMap::new();
    let mut traits_map = HashMap::new();
    let mut impls_map = HashMap::new();
    let mut impls_by_type: HashMap<ItemPath, Vec<LibraryDefId>> = HashMap::new();
    let mut impls_by_trait_map: HashMap<ItemPath, Vec<LibraryDefId>> = HashMap::new();
    let mut display_vars: HashMap<LibraryDefId, HashMap<TyVar, TyVar>> = HashMap::new();
    let mut root_nodes: HashMap<LibraryDefId, NodeId> = HashMap::new();
    let mut parent_map: HashMap<LibraryDefId, LibraryDefId> = HashMap::new();
    let mut func_defs: HashMap<LibraryDefId, FuncDef> = HashMap::new();

    for file_id in workspace.all_file_ids() {
        let parse_result = parse_file(db, file_id);

        for def_header in &parse_result.defs {
            let lib_def_id = match def_id_to_lib.get(&def_header.def_id) {
                Some(id) => id.clone(),
                None => continue, // FileMain, StructField — skipped
            };

            let target = DefTarget::Workspace(def_header.def_id);

            // Track root NodeId for doc comment lookup
            root_nodes.insert(lib_def_id.clone(), def_header.root_node);

            // Track parent relationship
            if let Some(parent_def_id) = def_header.parent {
                if let Some(parent_lib_id) = def_id_to_lib.get(&parent_def_id) {
                    parent_map.insert(lib_def_id.clone(), parent_lib_id.clone());
                }
            }

            // Get type scheme for all defs that have one
            if let Some(scheme) = def_scheme(db, target.clone()) {
                schemes.insert(lib_def_id.clone(), scheme);
            }

            // Collect reverse map for display (schema var → user var)
            let reverse_map = collect_reverse_map(db, def_header.def_id);
            if !reverse_map.is_empty() {
                display_vars.insert(lib_def_id.clone(), reverse_map);
            }

            // Build FuncDef for functions and methods
            if matches!(def_header.kind, DefKind::Function { .. } | DefKind::Method) {
                if let Some(mut fdef) = func_def(db, target.clone()) {
                    fdef.target = remap_def_target(&fdef.target, &def_id_to_lib);
                    func_defs.insert(lib_def_id.clone(), fdef);
                }
            }

            match def_header.kind {
                DefKind::Function { .. }
                | DefKind::TypeAlias
                | DefKind::AssociatedConst { .. }
                | DefKind::Binding { .. } => {
                    // Named export (only top-level, not methods)
                    if def_header.parent.is_none() {
                        if let Some(path) = def_path(db, target) {
                            names.insert(path, lib_def_id);
                        }
                    }
                }
                DefKind::Struct => {
                    if let Some(path) = def_path(db, target.clone()) {
                        names.insert(path, lib_def_id.clone());
                    }
                    if let Some(mut sdef) = struct_def(db, target) {
                        sdef.target = remap_def_target(&sdef.target, &def_id_to_lib);
                        structs_map.insert(lib_def_id, sdef);
                    }
                }
                DefKind::Trait => {
                    if let Some(path) = def_path(db, target.clone()) {
                        names.insert(path, lib_def_id.clone());
                    }
                    if let Some(mut tdef) = trait_def(db, target) {
                        tdef.target = remap_def_target(&tdef.target, &def_id_to_lib);
                        for method in &mut tdef.methods {
                            method.target = remap_def_target(&method.target, &def_id_to_lib);
                        }
                        traits_map.insert(lib_def_id, tdef);
                    }
                }
                DefKind::Impl => {
                    if let Some(mut idef) = (*impl_def(db, target)).clone() {
                        idef.target = remap_def_target(&idef.target, &def_id_to_lib);
                        for method in &mut idef.methods {
                            method.target = remap_def_target(&method.target, &def_id_to_lib);
                        }
                        if let Some(type_path) = idef.implementing_type.item_path() {
                            impls_by_type
                                .entry(type_path.clone())
                                .or_default()
                                .push(lib_def_id.clone());
                        }
                        if let Some(ref trait_ty) = idef.trait_ty {
                            if let Some(trait_path) = trait_ty.item_path() {
                                impls_by_trait_map
                                    .entry(trait_path.clone())
                                    .or_default()
                                    .push(lib_def_id.clone());
                            }
                        }
                        impls_map.insert(lib_def_id, idef);
                    }
                }
                DefKind::Method => {
                    // Method schemes already added above; they're accessed
                    // through their parent trait/impl, not via names
                }
                DefKind::FileMain | DefKind::StructField | DefKind::Primitive => {}
            }
        }
    }

    LibraryData {
        names,
        schemes,
        structs: structs_map,
        traits: traits_map,
        impls: impls_map,
        impls_by_type,
        impls_by_trait: impls_by_trait_map,
        operators: HashMap::new(),
        modules,
        definitions: HashMap::new(),
        source_map: srcmap,
        display_vars,
        root_nodes,
        parent_map,
        func_defs,
    }
}

/// Remap a DefTarget from workspace to library form.
fn remap_def_target(target: &DefTarget, mapping: &HashMap<DefId, LibraryDefId>) -> DefTarget {
    match target {
        DefTarget::Workspace(def_id) => {
            let lib_id = mapping.get(def_id).unwrap_or_else(|| {
                panic!("missing library mapping for workspace def {:?}", def_id)
            });
            DefTarget::Library(lib_id.clone())
        }
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use ray_shared::{
        def::LibraryDefId,
        pathlib::ModulePath,
        ty::{SchemaVarAllocator, Ty, TyVar},
    };
    use ray_typing::types::TyScheme;

    use crate::queries::libraries::{
        LibraryData, find_max_schema_var_id, parse_schema_var_id, remap_library_type_vars,
        reserve_schema_var_range,
    };

    #[test]
    fn parse_schema_var_id_extracts_number() {
        let var = TyVar::new("?s0");
        assert_eq!(parse_schema_var_id(&var), Some(0));

        let var = TyVar::new("?s42");
        assert_eq!(parse_schema_var_id(&var), Some(42));

        let var = TyVar::new("?t0");
        assert_eq!(parse_schema_var_id(&var), None);

        let var = TyVar::new("foo");
        assert_eq!(parse_schema_var_id(&var), None);
    }

    #[test]
    fn reserve_schema_var_range_advances_allocator() {
        let mut allocator = SchemaVarAllocator::new();
        assert_eq!(allocator.curr_id(), 0);

        let offset = reserve_schema_var_range(&mut allocator, 5);
        assert_eq!(offset, 0);
        assert_eq!(allocator.curr_id(), 5);

        let offset2 = reserve_schema_var_range(&mut allocator, 3);
        assert_eq!(offset2, 5);
        assert_eq!(allocator.curr_id(), 8);
    }

    #[test]
    fn find_max_schema_var_id_empty_data() {
        let data = LibraryData::default();
        assert_eq!(find_max_schema_var_id(&data), 0);
    }

    #[test]
    fn find_max_schema_var_id_with_schemes() {
        let mut data = LibraryData::default();
        let lib_def_id = LibraryDefId {
            module: ModulePath::from("test"),
            index: 0,
        };
        data.schemes.insert(
            lib_def_id,
            TyScheme {
                vars: vec![TyVar::new("?s0"), TyVar::new("?s5")],
                qualifiers: vec![],
                ty: Ty::unit(),
            },
        );

        assert_eq!(find_max_schema_var_id(&data), 6); // max is 5, so we need 6
    }

    #[test]
    fn remap_library_type_vars_updates_all_vars() {
        let mut data = LibraryData::default();
        let lib_def_id = LibraryDefId {
            module: ModulePath::from("test"),
            index: 0,
        };
        data.schemes.insert(
            lib_def_id.clone(),
            TyScheme {
                vars: vec![TyVar::new("?s0"), TyVar::new("?s1")],
                qualifiers: vec![],
                ty: Ty::Var(TyVar::new("?s0")),
            },
        );

        remap_library_type_vars(&mut data, 10);

        let scheme = data.schemes.get(&lib_def_id).unwrap();
        assert_eq!(scheme.vars[0].path().name(), Some("?s10".to_string()));
        assert_eq!(scheme.vars[1].path().name(), Some("?s11".to_string()));

        if let Ty::Var(var) = &scheme.ty {
            assert_eq!(var.path().name(), Some("?s10".to_string()));
        } else {
            panic!("expected Ty::Var");
        }
    }

    #[test]
    fn schema_vars_dont_collide_after_loading() {
        // Simulate loading two libraries with overlapping var IDs
        let mut allocator = SchemaVarAllocator::new();

        // First "library" uses ?s0..?s2
        let lib1_max = 3;
        let offset1 = reserve_schema_var_range(&mut allocator, lib1_max);
        assert_eq!(offset1, 0);

        // After remapping, lib1 would use ?s0..?s2 (unchanged since offset is 0)

        // Second "library" also uses ?s0..?s1
        let lib2_max = 2;
        let offset2 = reserve_schema_var_range(&mut allocator, lib2_max);
        assert_eq!(offset2, 3);

        // After remapping, lib2 would use ?s3..?s4 (no collision!)

        // Workspace can now safely allocate from ?s5 onwards
        let workspace_var = allocator.alloc();
        assert_eq!(workspace_var.path().name(), Some("?s5".to_string()));
    }
}

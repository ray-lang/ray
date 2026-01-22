use std::{
    collections::HashMap,
    fs::File,
    hash::{Hash, Hasher},
    io,
};

use ray_query_macros::{input, query};
use ray_shared::{
    pathlib::{FilePath, ItemPath, ModulePath},
    ty::{SCHEMA_PREFIX, SchemaVarAllocator, Ty, TyVar},
};
use ray_typing::types::{Subst, Substitutable};
use serde::{Deserialize, Serialize};

use crate::query::{Database, Input, Query};

/// Data extracted from a compiled library (.raylib file).
///
/// This contains the type schemes, structs, traits, impls, and operators
/// exported by the library. Schema variables are remapped during loading
/// to avoid collisions with workspace type inference variables.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct LibraryData {
    /// Type schemes for exported definitions, keyed by path.
    pub schemes: HashMap<ItemPath, LibraryScheme>,
    /// Struct definitions exported by the library.
    pub structs: Vec<LibraryStruct>,
    /// Trait definitions exported by the library.
    pub traits: Vec<LibraryTrait>,
    /// Impl blocks exported by the library.
    pub impls: Vec<LibraryImpl>,
    /// Operator definitions exported by the library.
    pub operators: Vec<LibraryOperator>,
    /// Module paths contained in this library.
    pub modules: Vec<ModulePath>,
}

/// A type scheme from a library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LibraryScheme {
    /// The quantified type variables.
    pub vars: Vec<TyVar>,
    /// Predicates/constraints on the scheme.
    pub predicates: Vec<Ty>,
    /// The body type.
    pub ty: Ty,
}

/// A struct definition from a library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LibraryStruct {
    pub path: ItemPath,
    pub type_params: Vec<TyVar>,
    pub fields: Vec<(String, Ty)>,
}

/// A trait definition from a library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LibraryTrait {
    pub path: ItemPath,
    pub type_params: Vec<TyVar>,
    pub super_traits: Vec<ItemPath>,
    pub methods: Vec<String>,
}

/// An impl block from a library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LibraryImpl {
    pub trait_path: Option<ItemPath>,
    pub self_ty: Ty,
    pub type_params: Vec<TyVar>,
    pub predicates: Vec<Ty>,
    pub methods: Vec<String>,
}

/// An operator definition from a library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LibraryOperator {
    pub name: String,
    pub precedence: u8,
    pub associativity: Associativity,
}

/// Operator associativity.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum Associativity {
    Left,
    Right,
    None,
}

/// Collection of loaded libraries, keyed by library path.
///
/// This is a singleton input (keyed by `()`) that stores all loaded library data.
/// Libraries are loaded at startup and their exports are used for name resolution.
#[input(key = "()")]
#[derive(Clone, Debug, Default)]
pub struct LoadedLibraries {
    /// Library data keyed by the library's module path (e.g., "core", "std").
    pub libraries: HashMap<ModulePath, LibraryData>,
}

impl Hash for LoadedLibraries {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash library paths in sorted order for determinism
        let mut keys: Vec<_> = self.libraries.keys().collect();
        keys.sort_by_key(|k| k.to_string());
        for path in keys {
            path.hash(state);
        }
    }
}

impl LoadedLibraries {
    /// Add a library to the collection.
    pub fn add(&mut self, lib_path: ModulePath, data: LibraryData) {
        self.libraries.insert(lib_path, data);
    }

    /// Get a library by its path.
    pub fn get(&self, lib_path: &ModulePath) -> Option<&LibraryData> {
        self.libraries.get(lib_path)
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
pub fn library_data(db: &Database, module_path: ModulePath) -> Option<LibraryData> {
    let libraries = db.get_input::<LoadedLibraries>(());
    let lib_path = libraries.library_for_module(&module_path)?;
    libraries.get(lib_path).cloned()
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
    let mut data: LibraryData = bincode::deserialize_from(file)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

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
        for pred in &scheme.predicates {
            max_id = max_id.max(find_max_in_ty(pred));
        }
    }

    for s in &data.structs {
        for var in &s.type_params {
            if let Some(id) = parse_schema_var_id(var) {
                max_id = max_id.max(id + 1);
            }
        }
        for (_, ty) in &s.fields {
            max_id = max_id.max(find_max_in_ty(ty));
        }
    }

    for t in &data.traits {
        for var in &t.type_params {
            if let Some(id) = parse_schema_var_id(var) {
                max_id = max_id.max(id + 1);
            }
        }
    }

    for imp in &data.impls {
        for var in &imp.type_params {
            if let Some(id) = parse_schema_var_id(var) {
                max_id = max_id.max(id + 1);
            }
        }
        max_id = max_id.max(find_max_in_ty(&imp.self_ty));
        for pred in &imp.predicates {
            max_id = max_id.max(find_max_in_ty(pred));
        }
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
        scheme.predicates.apply_subst(&subst);
    }

    for s in &mut data.structs {
        s.type_params.apply_subst(&subst);
        for (_, ty) in &mut s.fields {
            ty.apply_subst(&subst);
        }
    }

    for t in &mut data.traits {
        t.type_params.apply_subst(&subst);
    }

    for imp in &mut data.impls {
        imp.type_params.apply_subst(&subst);
        imp.self_ty.apply_subst(&subst);
        imp.predicates.apply_subst(&subst);
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
        for pred in &scheme.predicates {
            collect_vars_from_ty(&mut subst, pred, offset);
        }
    }

    for s in &data.structs {
        for var in &s.type_params {
            add_var_to_subst(&mut subst, var, offset);
        }
        for (_, ty) in &s.fields {
            collect_vars_from_ty(&mut subst, ty, offset);
        }
    }

    for t in &data.traits {
        for var in &t.type_params {
            add_var_to_subst(&mut subst, var, offset);
        }
    }

    for imp in &data.impls {
        for var in &imp.type_params {
            add_var_to_subst(&mut subst, var, offset);
        }
        collect_vars_from_ty(&mut subst, &imp.self_ty, offset);
        for pred in &imp.predicates {
            collect_vars_from_ty(&mut subst, pred, offset);
        }
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

#[cfg(test)]
mod tests {
    use ray_shared::{
        pathlib::{ItemPath, ModulePath},
        ty::{SchemaVarAllocator, Ty, TyVar},
    };

    use crate::queries::libraries::{
        LibraryData, LibraryScheme, find_max_schema_var_id, parse_schema_var_id,
        remap_library_type_vars, reserve_schema_var_range,
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
        data.schemes.insert(
            ItemPath {
                module: ModulePath::from("test"),
                item: vec!["foo".to_string()],
            },
            LibraryScheme {
                vars: vec![TyVar::new("?s0"), TyVar::new("?s5")],
                predicates: vec![],
                ty: Ty::unit(),
            },
        );

        assert_eq!(find_max_schema_var_id(&data), 6); // max is 5, so we need 6
    }

    #[test]
    fn remap_library_type_vars_updates_all_vars() {
        let mut data = LibraryData::default();
        data.schemes.insert(
            ItemPath {
                module: ModulePath::from("test"),
                item: vec!["foo".to_string()],
            },
            LibraryScheme {
                vars: vec![TyVar::new("?s0"), TyVar::new("?s1")],
                predicates: vec![],
                ty: Ty::Var(TyVar::new("?s0")),
            },
        );

        remap_library_type_vars(&mut data, 10);

        let scheme = data
            .schemes
            .get(&ItemPath {
                module: ModulePath::from("test"),
                item: vec!["foo".to_string()],
            })
            .unwrap();
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

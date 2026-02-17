//! Display information queries for hover and other IDE features.
//!
//! Provides rust-analyzer-style provenance display: when hovering over a method,
//! the user sees the containing type, the impl/trait block, and the method signature.

use std::collections::HashMap;

use ray_core::ast::Modifier;
use ray_query_macros::query;
use ray_shared::{
    def::{DefId, DefKind, LibraryDefId},
    resolution::DefTarget,
    ty::{Ty, TyVar},
};
use ray_typing::{
    constraints::Predicate,
    types::{Subst, Substitutable, TyScheme},
};
use serde::{Deserialize, Serialize};

use crate::{
    queries::{
        defs::{def_header, definition_record, func_def, impl_def, struct_def, trait_def},
        libraries::library_data,
        typecheck::def_scheme,
        types::mapped_def_types,
    },
    query::{Database, Query},
};

/// Display information for a definition, used for hover tooltips.
///
/// Contains a provenance chain of signatures (outermost container first)
/// and an optional documentation comment.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DefDisplayInfo {
    /// Provenance chain of signatures, outermost first.
    ///
    /// Example for a trait impl method:
    ///   `["List['a]", "impl Eq[List['a]]", "pub fn eq(self, other: List['a]) -> bool"]`
    pub signatures: Vec<String>,
    /// Documentation comment, if any.
    pub doc: Option<String>,
}

/// Get display information for a definition.
///
/// Returns a `DefDisplayInfo` containing a provenance chain of signatures
/// and an optional documentation comment. Used by the hover handler to
/// show rust-analyzer-style contextual information.
///
/// Works uniformly for workspace, library, and primitive definitions.
#[query]
pub fn def_display_info(db: &Database, target: DefTarget) -> Option<DefDisplayInfo> {
    let record = definition_record(db, target.clone())?;
    let name = record.path.item_name().unwrap_or("?").to_string();

    let mut signatures = Vec::new();

    match record.kind {
        DefKind::Primitive => {
            return Some(DefDisplayInfo {
                signatures: vec![name],
                doc: record.doc,
            });
        }

        DefKind::FileMain | DefKind::Test => {
            return None;
        }

        DefKind::Function { .. } | DefKind::Method => {
            if let Some(ref parent_target) = record.parent {
                // Method or function with a parent (impl/trait)
                let parent_record = definition_record(db, parent_target.clone());

                match parent_record.as_ref().map(|r| r.kind) {
                    Some(DefKind::Impl) => {
                        let impl_arc = impl_def(db, parent_target.clone());
                        let impl_info = impl_arc.as_ref().as_ref();

                        if let Some(info) = impl_info {
                            let impl_ty =
                                display_ty_for_target(db, parent_target, &info.implementing_type);
                            let display_preds =
                                display_predicates_for_target(db, parent_target, &info.predicates);

                            if let Some(ref trait_ty) = info.trait_ty {
                                let display_trait_ty =
                                    display_ty_for_target(db, parent_target, trait_ty);
                                signatures.push(format_impl_sig(
                                    &impl_ty,
                                    Some(&display_trait_ty),
                                    &display_preds,
                                ));
                            } else {
                                signatures.push(format_impl_sig(&impl_ty, None, &display_preds));
                            }
                        }

                        let parent_params = impl_info.map(|info| {
                            (
                                parent_target as &DefTarget,
                                info.type_params.as_slice(),
                                info.predicates.as_slice(),
                            )
                        });
                        let sig = format_func_sig_from_query(db, &target, &name, parent_params);
                        signatures.push(sig);
                    }
                    Some(DefKind::Trait) => {
                        let tdef_opt = trait_def(db, parent_target.clone());
                        if let Some(ref tdef) = tdef_opt {
                            let vars = format_ty_vars(&display_vars_for_target(
                                db,
                                parent_target,
                                &tdef.type_params,
                            ));
                            let trait_name = tdef.path.item_name().unwrap_or("?");
                            signatures.push(format!("trait {}{}", trait_name, vars));
                        }
                        let parent_params = tdef_opt.as_ref().map(|tdef| {
                            (
                                parent_target as &DefTarget,
                                tdef.type_params.as_slice(),
                                [].as_slice(),
                            )
                        });
                        let sig = format_func_sig_from_query(db, &target, &name, parent_params);
                        signatures.push(sig);
                    }
                    _ => {
                        let sig = format_func_sig_from_query(db, &target, &name, None);
                        signatures.push(sig);
                    }
                }
            } else {
                // Standalone function (no parent)
                if !record.path.module.is_empty() {
                    signatures.push(record.path.module.to_string());
                }
                let sig = format_func_sig_from_query(db, &target, &name, None);
                signatures.push(sig);
            }
        }

        DefKind::Struct => {
            if !record.path.module.is_empty() {
                signatures.push(record.path.module.to_string());
            }
            let vars = struct_def(db, target.clone())
                .map(|sdef| format_ty_vars(&display_vars_for_target(db, &target, &sdef.ty.vars)))
                .unwrap_or_default();
            signatures.push(format!("struct {}{}", name, vars));
        }

        DefKind::StructField => {
            if let Some(ref parent_target) = record.parent {
                let parent_name = definition_record(db, parent_target.clone())
                    .and_then(|r| r.path.item_name().map(|n| n.to_string()))
                    .unwrap_or_else(|| "?".to_string());
                let sdef = struct_def(db, parent_target.clone());
                let vars = sdef
                    .as_ref()
                    .map(|s| {
                        format_ty_vars(&display_vars_for_target(db, parent_target, &s.ty.vars))
                    })
                    .unwrap_or_default();
                signatures.push(format!("struct {}{}", parent_name, vars));

                let field_ty_str = sdef
                    .and_then(|sdef| {
                        sdef.fields.iter().find(|f| f.name == name).map(|field| {
                            display_ty_for_target(db, &target, &field.ty.ty).to_string()
                        })
                    })
                    .unwrap_or_else(|| "?".to_string());
                signatures.push(format!("{}: {}", name, field_ty_str));
            } else {
                signatures.push(format!("{}: ?", name));
            }
        }

        DefKind::Trait => {
            if !record.path.module.is_empty() {
                signatures.push(record.path.module.to_string());
            }
            let vars = trait_def(db, target.clone())
                .map(|tdef| {
                    format_ty_vars(&display_vars_for_target(db, &target, &tdef.type_params))
                })
                .unwrap_or_default();
            signatures.push(format!("trait {}{}", name, vars));
        }

        DefKind::Impl => {
            if let Some(impl_info) = impl_def(db, target.clone()).as_ref() {
                let impl_ty = display_ty_for_target(db, &target, &impl_info.implementing_type);
                let trait_display_ty = impl_info
                    .trait_ty
                    .as_ref()
                    .map(|ty| display_ty_for_target(db, &target, ty));
                let display_preds =
                    display_predicates_for_target(db, &target, &impl_info.predicates);
                signatures.push(format_impl_sig(
                    &impl_ty,
                    trait_display_ty.as_ref(),
                    &display_preds,
                ));
            } else {
                signatures.push(format!("impl {}", name));
            }
        }

        DefKind::TypeAlias => {
            let scheme = get_display_scheme(db, &target);
            if let Some(scheme) = scheme {
                let vars = format_ty_vars(&scheme.vars);
                signatures.push(format!("typealias {}{} = {}", name, vars, scheme.ty));
            } else {
                signatures.push(format!("typealias {}", name));
            }
        }

        DefKind::Binding { .. } | DefKind::AssociatedConst { .. } => {
            let scheme = get_display_scheme(db, &target);
            let ty_str = scheme
                .map(|s| s.ty.to_string())
                .unwrap_or_else(|| "?".to_string());
            signatures.push(format!("{}: {}", name, ty_str));
        }
    }

    if signatures.is_empty() {
        return None;
    }

    Some(DefDisplayInfo {
        signatures,
        doc: record.doc,
    })
}

// ============================================================================
// Function signature formatting
// ============================================================================

/// Format a function/method signature using query results only.
///
/// Uses `func_def` for param names and modifiers, `get_display_scheme` for types.
/// When parent type vars and predicates are provided, inherited vars and qualifiers
/// are stripped using the parent's display-mapped vars/predicates.
fn format_func_sig_from_query(
    db: &Database,
    target: &DefTarget,
    name: &str,
    parent_type_params: Option<(&DefTarget, &[TyVar], &[Predicate])>,
) -> String {
    let fdef = func_def(db, target.clone());
    let scheme = get_display_scheme(db, target);

    let (param_names, modifiers): (&[String], &[Modifier]) = match fdef {
        Some(ref fd) => (&fd.param_names, &fd.modifiers),
        None => (&[], &[]),
    };

    // Build display-mapped parent vars and predicates for filtering
    let parent_display = parent_type_params.map(|(pt, vars, preds)| {
        let display_vars = display_vars_for_target(db, pt, vars);
        let display_preds = display_predicates_for_target(db, pt, preds);
        (display_vars, display_preds)
    });

    match scheme {
        Some(scheme) => format_func_display(
            name,
            &scheme,
            param_names,
            modifiers,
            parent_display.as_ref(),
        ),
        None => {
            let mut parts = Vec::new();
            for m in modifiers {
                parts.push(m.to_string());
            }
            parts.push(format!("fn {}", name));
            parts.join(" ")
        }
    }
}

/// Format a function signature from its components.
///
/// Combines modifiers, name, type vars, params (with names if available),
/// return type, and where-clause. Strips parent vars and qualifiers
/// when `parent_display` is provided (display-mapped parent vars and predicates).
pub fn format_func_display(
    name: &str,
    scheme: &TyScheme,
    param_names: &[String],
    modifiers: &[Modifier],
    parent_display: Option<&(Vec<TyVar>, Vec<Predicate>)>,
) -> String {
    let mut parts = Vec::new();

    for m in modifiers {
        parts.push(m.to_string());
    }
    parts.push("fn".to_string());

    // Strip parent impl vars and qualifiers from the method scheme
    let (vars, qualifiers) = if let Some((parent_vars, parent_preds)) = parent_display {
        let filtered_vars: Vec<_> = scheme
            .vars
            .iter()
            .filter(|v| !parent_vars.contains(v))
            .cloned()
            .collect();
        let parent_qual_strs: Vec<_> = parent_preds.iter().map(|p| p.to_string()).collect();
        let filtered_quals: Vec<_> = scheme
            .qualifiers
            .iter()
            .filter(|q| !parent_qual_strs.contains(&q.to_string()))
            .cloned()
            .collect();
        (filtered_vars, filtered_quals)
    } else {
        (scheme.vars.clone(), scheme.qualifiers.clone())
    };

    let vars_str = format_ty_vars(&vars);
    let params_str = format_func_params(param_names, &scheme.ty);
    let ret_str = format_func_ret(&scheme.ty);
    let quals_str = format_qualifiers(&qualifiers);

    let sig_str = format!("{}{}{}{}", name, vars_str, params_str, ret_str);
    parts.push(sig_str);

    let result = parts.join(" ");
    if quals_str.is_empty() {
        result
    } else {
        format!("{} where {}", result, quals_str)
    }
}

/// Format function parameters from names + types in Ty::Func.
///
/// When param_names is non-empty, produces `(name: type, ...)`.
/// When param_names is empty, produces `(type, ...)`.
/// Self params are formatted specially (just `self` when type is `self`).
pub fn format_func_params(param_names: &[String], ty: &Ty) -> String {
    match ty {
        Ty::Func(param_tys, _) => {
            if param_names.is_empty() {
                // No names available — just show types
                let params_str = param_tys
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({})", params_str)
            } else {
                let params: Vec<String> = param_names
                    .iter()
                    .zip(param_tys.iter())
                    .map(|(name, ty)| format!("{}: {}", name, ty))
                    .collect();

                // Handle extra types without corresponding names
                let extra: Vec<String> = param_tys
                    .iter()
                    .skip(param_names.len())
                    .map(|ty| ty.to_string())
                    .collect();

                let mut all_params = params;
                all_params.extend(extra);

                format!("({})", all_params.join(", "))
            }
        }
        _ => {
            if param_names.is_empty() {
                "()".to_string()
            } else {
                format!("({})", param_names.join(", "))
            }
        }
    }
}

/// Extract the return type string from a Ty::Func.
pub fn format_func_ret(ty: &Ty) -> String {
    match ty {
        Ty::Func(_, ret) => format!(" -> {}", ret),
        _ => String::new(),
    }
}

// ============================================================================
// Display type variable mapping (schema vars → user vars)
// ============================================================================

/// Get the type scheme for display, with internal vars renamed to user vars.
///
/// Fetches `def_scheme`, then applies the `reverse_map` from `mapped_def_types`
/// (and parent's `mapped_def_types`) to rename internal vars like `?s:...` to
/// user-facing names like `'a`.
fn get_display_scheme(db: &Database, target: &DefTarget) -> Option<TyScheme> {
    let mut scheme = def_scheme(db, target.clone())?;

    let reverse_map = match target {
        DefTarget::Workspace(def_id) => Some(collect_reverse_map(db, *def_id)),
        DefTarget::Library(lib_def_id) => library_reverse_map(db, lib_def_id),
        DefTarget::Primitive(_) | DefTarget::Module(_) => None,
    };

    if let Some(ref map) = reverse_map {
        if !map.is_empty() {
            let subst = build_rename_subst(map);
            scheme.apply_subst(&subst);
        }
    }

    Some(scheme)
}

/// Collect the full reverse_map for a definition, including parent mappings.
pub(crate) fn collect_reverse_map(db: &Database, def_id: DefId) -> HashMap<TyVar, TyVar> {
    let mut reverse_map = HashMap::new();

    // Get parent's reverse_map first (for methods in trait/impl blocks)
    if let Some(header) = def_header(db, def_id) {
        if let Some(parent_id) = header.parent {
            let parent_mapping = mapped_def_types(db, parent_id);
            reverse_map.extend(
                parent_mapping
                    .reverse_map
                    .iter()
                    .map(|(k, v)| (k.clone(), v.clone())),
            );
        }
    }

    // Get own reverse_map (may override parent entries)
    let mapping = mapped_def_types(db, def_id);
    reverse_map.extend(
        mapping
            .reverse_map
            .iter()
            .map(|(k, v)| (k.clone(), v.clone())),
    );

    reverse_map
}

/// Build a Subst from a reverse_map (schema_var → user_var).
pub fn build_rename_subst(reverse_map: &HashMap<TyVar, TyVar>) -> Subst {
    let mut subst = Subst::new();
    for (schema_var, user_var) in reverse_map {
        subst.insert(schema_var.clone(), Ty::Var(user_var.clone()));
    }
    subst
}

/// Apply the reverse variable mapping to a monomorphic type for display.
///
/// Replaces internal schema variables (like `?s:2d321b8899014831:0`) with
/// user-facing names (like `'k`, `'v`) based on the owning definition's
/// type parameter mapping (and its parent's, for methods in impl/trait blocks).
pub fn display_ty(db: &Database, owner: DefId, ty: &Ty) -> Ty {
    let reverse_map = collect_reverse_map(db, owner);
    if reverse_map.is_empty() {
        return ty.clone();
    }
    let subst = build_rename_subst(&reverse_map);
    let mut result = ty.clone();
    result.apply_subst(&subst);
    result
}

/// Apply the reverse variable mapping to a type from any DefTarget.
///
/// Works for workspace, library, and primitive definitions.
fn display_ty_for_target(db: &Database, target: &DefTarget, ty: &Ty) -> Ty {
    match target {
        DefTarget::Workspace(def_id) => display_ty(db, *def_id, ty),
        DefTarget::Library(lib_def_id) => display_library_ty(db, lib_def_id, ty),
        DefTarget::Primitive(_) | DefTarget::Module(_) => ty.clone(),
    }
}

/// Apply the reverse variable mapping to type vars from any DefTarget.
///
/// Maps internal schema vars (like `?s:...`) to user-facing names (like `'a`).
fn display_vars_for_target(db: &Database, target: &DefTarget, vars: &[TyVar]) -> Vec<TyVar> {
    let reverse_map = match target {
        DefTarget::Workspace(def_id) => {
            let map = collect_reverse_map(db, *def_id);
            if map.is_empty() {
                return vars.to_vec();
            }
            map
        }
        DefTarget::Library(lib_def_id) => match library_reverse_map(db, lib_def_id) {
            Some(map) if !map.is_empty() => map,
            _ => return vars.to_vec(),
        },
        DefTarget::Primitive(_) | DefTarget::Module(_) => return vars.to_vec(),
    };
    vars.iter()
        .map(|v| reverse_map.get(v).cloned().unwrap_or_else(|| v.clone()))
        .collect()
}

/// Apply the reverse variable mapping to predicates from any DefTarget.
fn display_predicates_for_target(
    db: &Database,
    target: &DefTarget,
    predicates: &[Predicate],
) -> Vec<Predicate> {
    let reverse_map = match target {
        DefTarget::Workspace(def_id) => {
            let map = collect_reverse_map(db, *def_id);
            if map.is_empty() {
                return predicates.to_vec();
            }
            map
        }
        DefTarget::Library(lib_def_id) => match library_reverse_map(db, lib_def_id) {
            Some(map) if !map.is_empty() => map,
            _ => return predicates.to_vec(),
        },
        DefTarget::Primitive(_) | DefTarget::Module(_) => return predicates.to_vec(),
    };
    let subst = build_rename_subst(&reverse_map);
    predicates
        .iter()
        .map(|p| {
            let mut p = p.clone();
            p.apply_subst(&subst);
            p
        })
        .collect()
}

/// Look up the display reverse map for a library definition.
fn library_reverse_map(db: &Database, lib_def_id: &LibraryDefId) -> Option<HashMap<TyVar, TyVar>> {
    let data = library_data(db, lib_def_id.module.clone())?;
    data.display_vars.get(lib_def_id).cloned()
}

/// Apply the reverse variable mapping to a type from a library definition.
///
/// Like `display_ty` but for library definitions, using the serialized
/// reverse map from `LibraryData.display_vars`.
pub fn display_library_ty(db: &Database, lib_def_id: &LibraryDefId, ty: &Ty) -> Ty {
    let reverse_map = library_reverse_map(db, lib_def_id);
    match reverse_map {
        Some(ref map) if !map.is_empty() => {
            let subst = build_rename_subst(map);
            let mut result = ty.clone();
            result.apply_subst(&subst);
            result
        }
        _ => ty.clone(),
    }
}

// ============================================================================
// Formatting helpers
// ============================================================================

/// Format type variables as `[var1, var2]`, or empty string if none.
pub fn format_ty_vars(vars: &[TyVar]) -> String {
    if vars.is_empty() {
        String::new()
    } else {
        let vars_str = vars
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!("[{}]", vars_str)
    }
}

/// Format qualifiers/predicates as a where clause body (without the `where` keyword).
pub fn format_qualifiers(qualifiers: &[Predicate]) -> String {
    if qualifiers.is_empty() {
        String::new()
    } else {
        qualifiers
            .iter()
            .map(|q| q.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// Format an impl signature, including where-clause predicates if any.
pub fn format_impl_sig(
    implementing_type: &Ty,
    trait_ty: Option<&Ty>,
    predicates: &[Predicate],
) -> String {
    let base = match trait_ty {
        Some(trait_ty) => format!("impl {}", trait_ty),
        None => format!("impl object {}", implementing_type),
    };
    let quals_str = format_qualifiers(predicates);
    if quals_str.is_empty() {
        base
    } else {
        format!("{} where {}", base, quals_str)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        def::LibraryDefId,
        file_id::FileId,
        node_id::NodeId,
        pathlib::{FilePath, ItemPath, ModulePath},
        resolution::DefTarget,
        ty::{Ty, TyVar},
    };
    use ray_typing::types::TyScheme;

    use crate::{
        queries::{
            defs::{FuncDef, StructDef, TraitDef},
            display::def_display_info,
            libraries::{LibraryData, LoadedLibraries},
            parse::parse_file,
            workspace::{FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

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

    fn find_def_by_name(db: &Database, file_id: FileId, name: &str) -> Option<DefTarget> {
        let parse_result = parse_file(db, file_id);
        parse_result
            .defs
            .iter()
            .find(|h| h.name == name)
            .map(|h| DefTarget::Workspace(h.def_id))
    }

    #[test]
    fn standalone_function_display() {
        let (db, file_id) = setup_db("fn add(x: int, y: int) -> int => x");
        let target = find_def_by_name(&db, file_id, "add").unwrap();
        let info = def_display_info(&db, target).unwrap();

        assert_eq!(info.signatures.len(), 2); // module_path + fn sig
        assert_eq!(info.signatures[0], "test");
        assert!(
            info.signatures[1].contains("fn"),
            "signature should contain 'fn': {}",
            info.signatures[1]
        );
        assert!(
            info.signatures[1].contains("add"),
            "signature should contain 'add': {}",
            info.signatures[1]
        );
    }

    #[test]
    fn struct_display() {
        let (db, file_id) = setup_db("struct Point { x: int, y: int }");
        let target = find_def_by_name(&db, file_id, "Point").unwrap();
        let info = def_display_info(&db, target).unwrap();

        // Should have module_path + struct sig
        assert!(info.signatures.len() >= 1);
        let struct_sig = info.signatures.last().unwrap();
        assert!(
            struct_sig.starts_with("struct Point"),
            "should start with 'struct Point': {}",
            struct_sig
        );
    }

    #[test]
    fn trait_display() {
        let source = r#"
trait Eq['a] {
    fn eq(self: 'a, other: 'a) -> bool
}
"#;
        let (db, file_id) = setup_db(source);
        let target = find_def_by_name(&db, file_id, "Eq").unwrap();
        let info = def_display_info(&db, target).unwrap();

        let trait_sig = info.signatures.last().unwrap();
        assert!(
            trait_sig.contains("trait Eq"),
            "should contain 'trait Eq': {}",
            trait_sig
        );
        assert!(
            trait_sig.contains("'a"),
            "should contain type var 'a: {}",
            trait_sig
        );
    }

    #[test]
    fn primitive_display() {
        let path = ItemPath::new(ModulePath::root(), vec!["int".into()]);
        let target = DefTarget::Primitive(path);
        let db = Database::new();

        let info = def_display_info(&db, target).unwrap();
        assert_eq!(info.signatures, vec!["int"]);
    }

    #[test]
    fn struct_field_display() {
        let (db, file_id) = setup_db("struct Point { x: int, y: int }");
        let target = find_def_by_name(&db, file_id, "x").unwrap();
        let info = def_display_info(&db, target).unwrap();

        // Should show parent struct + field type
        assert!(info.signatures.len() >= 2);
        assert!(
            info.signatures[0].contains("struct Point"),
            "first sig should contain 'struct Point': {}",
            info.signatures[0]
        );
        assert!(
            info.signatures[1].contains("x"),
            "second sig should contain 'x': {}",
            info.signatures[1]
        );
    }

    #[test]
    fn trait_method_display() {
        let source = "trait Eq['a] {\n    fn eq(self: 'a, other: 'a) -> bool\n}";
        let (db, file_id) = setup_db(source);

        let target = find_def_by_name(&db, file_id, "eq").unwrap();
        let info = def_display_info(&db, target).unwrap();

        // Should show: trait Eq['a], fn eq['a](self, other: 'a) -> bool
        assert_eq!(info.signatures.len(), 2);
        assert!(
            info.signatures[0].contains("trait Eq"),
            "first sig should be trait: {}",
            info.signatures[0]
        );
        assert!(
            info.signatures[0].contains("'a"),
            "trait sig should contain type var 'a: {}",
            info.signatures[0]
        );
        assert!(
            info.signatures[1].contains("fn eq"),
            "second sig should be method: {}",
            info.signatures[1]
        );
        // Verify user-facing type vars ('a) instead of internal vars (?s:...)
        assert!(
            info.signatures[1].contains("'a"),
            "should use user var names: {}",
            info.signatures[1]
        );
        assert!(
            !info.signatures[1].contains("?s:"),
            "should not contain internal var names: {}",
            info.signatures[1]
        );
    }

    // ========================================================================
    // Expanded workspace tests
    // ========================================================================

    #[test]
    fn inherent_impl_method_display() {
        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn origin() -> Point => Point { x: 0, y: 0 }
}
"#;
        let (db, file_id) = setup_db(source);
        let target = find_def_by_name(&db, file_id, "origin").unwrap();
        let info = def_display_info(&db, target).unwrap();

        // Should show: impl object <type>, fn origin() -> Point
        assert_eq!(info.signatures.len(), 2);
        assert!(
            info.signatures[0].contains("impl object"),
            "first sig should be impl: {}",
            info.signatures[0]
        );
        assert!(
            info.signatures[0].contains("Point"),
            "first sig should mention Point: {}",
            info.signatures[0]
        );
        assert!(
            info.signatures[1].contains("fn origin"),
            "second sig should be method: {}",
            info.signatures[1]
        );
    }

    #[test]
    fn trait_impl_method_display() {
        let source = r#"
trait Eq['a] {
    fn eq(self: 'a, other: 'a) -> bool
}

struct Point { x: int, y: int }

impl Eq[Point] {
    fn eq(self: Point, other: Point) -> bool => true
}
"#;
        let (db, file_id) = setup_db(source);
        // Find the impl method (second "eq"), not the trait method (first "eq")
        let parse_result = parse_file(&db, file_id);
        let impl_eq = parse_result
            .defs
            .iter()
            .filter(|h| h.name == "eq")
            .last()
            .expect("expected impl eq method");
        let target = DefTarget::Workspace(impl_eq.def_id);
        let info = def_display_info(&db, target).unwrap();

        // Should show: impl <Trait>[<Type>], fn eq(...)
        assert_eq!(info.signatures.len(), 2);
        assert!(
            info.signatures[0].contains("impl"),
            "first sig should be trait impl: {}",
            info.signatures[0]
        );
        assert!(
            info.signatures[0].contains("Eq"),
            "first sig should mention Eq: {}",
            info.signatures[0]
        );
        assert!(
            info.signatures[0].contains("Point"),
            "first sig should mention Point: {}",
            info.signatures[0]
        );
        assert!(
            info.signatures[1].contains("fn eq"),
            "second sig should be method: {}",
            info.signatures[1]
        );
    }

    #[test]
    fn generic_function_display() {
        let source = "fn identity['a](x: 'a) -> 'a => x";
        let (db, file_id) = setup_db(source);
        let target = find_def_by_name(&db, file_id, "identity").unwrap();
        let info = def_display_info(&db, target).unwrap();

        assert_eq!(info.signatures.len(), 2); // module_path + fn sig
        assert_eq!(info.signatures[0], "test");
        assert!(
            info.signatures[1].contains("identity"),
            "should contain function name: {}",
            info.signatures[1]
        );
        assert!(
            info.signatures[1].contains("'a"),
            "should contain type var 'a: {}",
            info.signatures[1]
        );
    }

    #[test]
    fn pub_function_display() {
        let source = "pub fn greet(name: string) -> string => name";
        let (db, file_id) = setup_db(source);
        let target = find_def_by_name(&db, file_id, "greet").unwrap();
        let info = def_display_info(&db, target).unwrap();

        assert_eq!(info.signatures.len(), 2);
        assert!(
            info.signatures[1].starts_with("pub fn greet"),
            "should start with 'pub fn greet': {}",
            info.signatures[1]
        );
    }

    #[test]
    #[ignore = "Parser does not yet support typealias declarations"]
    fn typealias_display() {
        let source = "typealias Pair = (int, int)";
        let (db, file_id) = setup_db(source);
        let target = find_def_by_name(&db, file_id, "Pair").unwrap();
        let info = def_display_info(&db, target).unwrap();

        assert!(info.signatures.len() >= 1);
        let sig = info.signatures.last().unwrap();
        assert!(
            sig.contains("typealias Pair"),
            "should contain 'typealias Pair': {}",
            sig
        );
    }

    #[test]
    fn impl_block_display() {
        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn origin() -> Point => Point { x: 0, y: 0 }
}
"#;
        let (db, file_id) = setup_db(source);
        let parse_result = parse_file(&db, file_id);
        // Find the impl def itself (not a method inside it)
        let impl_def = parse_result
            .defs
            .iter()
            .find(|h| matches!(h.kind, ray_shared::def::DefKind::Impl))
            .expect("expected impl def");
        let target = DefTarget::Workspace(impl_def.def_id);
        let info = def_display_info(&db, target).unwrap();

        assert!(info.signatures.len() >= 1);
        assert!(
            info.signatures[0].contains("impl object"),
            "should contain 'impl object': {}",
            info.signatures[0]
        );
        assert!(
            info.signatures[0].contains("Point"),
            "should mention Point: {}",
            info.signatures[0]
        );
    }

    #[test]
    fn doc_comment_display() {
        let source = "/// Adds two numbers together.\nfn add(x: int, y: int) -> int => x";
        let (db, file_id) = setup_db(source);
        let target = find_def_by_name(&db, file_id, "add").unwrap();
        let info = def_display_info(&db, target).unwrap();

        assert!(info.doc.is_some(), "should have a doc comment, got None");
        assert!(
            info.doc.as_ref().unwrap().contains("Adds two numbers"),
            "doc should contain 'Adds two numbers': {:?}",
            info.doc
        );
    }

    #[test]
    fn generic_struct_field_display() {
        let source = "struct Pair['a, 'b] { first: 'a, second: 'b }";
        let (db, file_id) = setup_db(source);
        let target = find_def_by_name(&db, file_id, "first").unwrap();
        let info = def_display_info(&db, target).unwrap();

        // Should show parent struct + field type
        assert!(info.signatures.len() >= 2);
        assert!(
            info.signatures[0].contains("struct Pair"),
            "first sig should be parent struct: {}",
            info.signatures[0]
        );
        assert!(
            info.signatures[1].contains("first"),
            "second sig should contain field name: {}",
            info.signatures[1]
        );
    }

    // ========================================================================
    // Library target tests
    // ========================================================================

    /// Helper to set up a database with library data and no workspace files.
    fn setup_library_db(lib_path: &str, lib_data: LibraryData) -> Database {
        let db = Database::new();
        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);

        let mut libraries = LoadedLibraries::default();
        libraries.add(ModulePath::from(lib_path), lib_data);
        db.set_input::<LoadedLibraries>((), libraries);

        db
    }

    #[test]
    fn library_function_display() {
        let mut lib = LibraryData::default();
        lib.modules.push(ModulePath::from("core::io"));

        let def_id = LibraryDefId {
            module: ModulePath::from("core::io"),
            index: 0,
        };
        let path = ItemPath::new(ModulePath::from("core::io"), vec!["read".into()]);

        lib.register_name(path.clone(), def_id.clone());
        lib.schemes.insert(
            def_id.clone(),
            TyScheme::from_mono(Ty::Func(vec![Ty::string()], Box::new(Ty::int()))),
        );

        let db = setup_library_db("core", lib);
        let target = DefTarget::Library(def_id);
        let info = def_display_info(&db, target).unwrap();

        // Should show module path + function signature
        assert!(info.signatures.len() >= 2);
        assert_eq!(info.signatures[0], "core::io");
        assert!(
            info.signatures[1].contains("fn read"),
            "should contain 'fn read': {}",
            info.signatures[1]
        );
    }

    #[test]
    fn library_function_with_param_names_display() {
        let mut lib = LibraryData::default();
        lib.modules.push(ModulePath::from("core::io"));

        let def_id = LibraryDefId {
            module: ModulePath::from("core::io"),
            index: 0,
        };
        let path = ItemPath::new(ModulePath::from("core::io"), vec!["write".into()]);
        let target = DefTarget::Library(def_id.clone());

        let func_ty = Ty::Func(vec![Ty::string(), Ty::int()], Box::new(Ty::unit()));
        let scheme = TyScheme::from_mono(func_ty.clone());

        lib.register_name(path.clone(), def_id.clone());
        lib.schemes.insert(def_id.clone(), scheme.clone());
        lib.func_defs.insert(
            def_id.clone(),
            FuncDef {
                target: target.clone(),
                path: path.clone(),
                scheme,
                param_names: vec!["data".into(), "flags".into()],
                modifiers: vec![],
            },
        );

        let db = setup_library_db("core", lib);
        let info = def_display_info(&db, target).unwrap();

        assert!(info.signatures.len() >= 2);
        let fn_sig = &info.signatures[1];
        assert!(
            fn_sig.contains("data"),
            "should contain param name 'data': {}",
            fn_sig
        );
        assert!(
            fn_sig.contains("flags"),
            "should contain param name 'flags': {}",
            fn_sig
        );
    }

    #[test]
    fn library_struct_display() {
        let mut lib = LibraryData::default();
        lib.modules.push(ModulePath::from("core::option"));

        let def_id = LibraryDefId {
            module: ModulePath::from("core::option"),
            index: 0,
        };
        let path = ItemPath::new(ModulePath::from("core::option"), vec!["Option".into()]);

        let ty_var = TyVar::from("'a");
        lib.register_name(path.clone(), def_id.clone());
        lib.schemes.insert(
            def_id.clone(),
            TyScheme {
                vars: vec![ty_var.clone()],
                qualifiers: vec![],
                ty: Ty::Const(path.clone()),
            },
        );
        lib.structs.insert(
            def_id.clone(),
            StructDef {
                target: DefTarget::Library(def_id.clone()),
                path: path.clone(),
                ty: TyScheme {
                    vars: vec![ty_var],
                    qualifiers: vec![],
                    ty: Ty::Const(path.clone()),
                },
                fields: vec![],
            },
        );

        let db = setup_library_db("core", lib);
        let target = DefTarget::Library(def_id);
        let info = def_display_info(&db, target).unwrap();

        let struct_sig = info.signatures.last().unwrap();
        assert!(
            struct_sig.contains("struct Option"),
            "should contain 'struct Option': {}",
            struct_sig
        );
        assert!(
            struct_sig.contains("'a"),
            "should contain type var: {}",
            struct_sig
        );
    }

    #[test]
    fn library_trait_display() {
        let mut lib = LibraryData::default();
        lib.modules.push(ModulePath::from("core::cmp"));

        let def_id = LibraryDefId {
            module: ModulePath::from("core::cmp"),
            index: 0,
        };
        let path = ItemPath::new(ModulePath::from("core::cmp"), vec!["Ord".into()]);

        let ty_var = TyVar::from("'a");
        lib.register_name(path.clone(), def_id.clone());
        lib.schemes.insert(
            def_id.clone(),
            TyScheme {
                vars: vec![ty_var.clone()],
                qualifiers: vec![],
                ty: Ty::Const(path.clone()),
            },
        );
        lib.traits.insert(
            def_id.clone(),
            TraitDef {
                target: DefTarget::Library(def_id.clone()),
                path: path.clone(),
                ty: Ty::Const(path.clone()),
                type_params: vec![ty_var],
                super_traits: vec![],
                methods: vec![],
                default_ty: None,
            },
        );

        let db = setup_library_db("core", lib);
        let target = DefTarget::Library(def_id);
        let info = def_display_info(&db, target).unwrap();

        let trait_sig = info.signatures.last().unwrap();
        assert!(
            trait_sig.contains("trait Ord"),
            "should contain 'trait Ord': {}",
            trait_sig
        );
        assert!(
            trait_sig.contains("'a"),
            "should contain type var: {}",
            trait_sig
        );
    }

    #[test]
    fn library_doc_comment_display() {
        let mut lib = LibraryData::default();
        lib.modules.push(ModulePath::from("core::io"));

        let def_id = LibraryDefId {
            module: ModulePath::from("core::io"),
            index: 0,
        };
        let path = ItemPath::new(ModulePath::from("core::io"), vec!["read".into()]);

        lib.register_name(path.clone(), def_id.clone());
        lib.schemes.insert(
            def_id.clone(),
            TyScheme::from_mono(Ty::Func(vec![Ty::string()], Box::new(Ty::int()))),
        );

        // Set up a doc comment via root_nodes + source_map
        let node_id = NodeId {
            owner: ray_shared::def::DefId {
                file: FileId(999),
                index: 0,
            },
            index: 0,
        };
        lib.root_nodes.insert(def_id.clone(), node_id);
        lib.source_map
            .set_doc_by_id(node_id, "Reads data from the stream.".into());

        let db = setup_library_db("core", lib);
        let target = DefTarget::Library(def_id);
        let info = def_display_info(&db, target).unwrap();

        assert!(info.doc.is_some(), "library def should have a doc comment");
        assert!(
            info.doc
                .as_ref()
                .unwrap()
                .contains("Reads data from the stream"),
            "doc should contain expected text: {:?}",
            info.doc
        );
    }
}

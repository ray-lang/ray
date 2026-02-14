//! Display information queries for hover and other IDE features.
//!
//! Provides rust-analyzer-style provenance display: when hovering over a method,
//! the user sees the containing type, the impl/trait block, and the method signature.

use std::collections::HashMap;

use ray_core::ast::{Decl, FuncSig, Node};
use ray_query_macros::query;
use ray_shared::{
    def::{DefId, DefKind, LibraryDefId},
    pathlib::ItemPath,
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
        defs::{ImplDef, def_header, def_path, impl_def, struct_def, trait_def},
        libraries::library_data,
        parse::parse_file,
        typecheck::def_scheme,
        types::{find_def_ast, mapped_def_types},
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
#[query]
pub fn def_display_info(db: &Database, target: DefTarget) -> Option<DefDisplayInfo> {
    match target {
        DefTarget::Workspace(def_id) => workspace_display_info(db, def_id),
        DefTarget::Library(_) => library_display_info(db, &target),
        DefTarget::Primitive(ref path) => {
            let name = path.item_name()?;
            Some(DefDisplayInfo {
                signatures: vec![name.to_string()],
                doc: None,
            })
        }
    }
}

fn workspace_display_info(db: &Database, def_id: DefId) -> Option<DefDisplayInfo> {
    let header = def_header(db, def_id)?;
    let target = DefTarget::Workspace(def_id);
    let item_path = def_path(db, target.clone());

    let parse_result = parse_file(db, def_id.file);
    let ast_node = find_def_ast(&parse_result.ast.decls, header.root_node);

    // Extract doc comment from AST if available
    let doc = ast_node.and_then(|node| extract_doc_comment(&node.value));

    let mut signatures = Vec::new();

    match header.kind {
        DefKind::Function { .. } if header.parent.is_none() => {
            // Standalone function: [module_path], fn signature
            if let Some(ref path) = item_path {
                if !path.module.is_empty() {
                    signatures.push(path.module.to_string());
                }
            }

            let sig_str = if let Some(node) = ast_node {
                format_func_from_ast(db, def_id, node, None)
            } else {
                format_func_from_scheme(db, &target, &header.name)
            };
            signatures.push(sig_str);
        }

        DefKind::Method if header.parent.is_some() => {
            let parent_def_id = header.parent.unwrap();
            let parent_header = def_header(db, parent_def_id);

            match parent_header.as_ref().map(|h| h.kind) {
                Some(DefKind::Impl) => {
                    // Method in an impl block
                    let parent_target = DefTarget::Workspace(parent_def_id);
                    let impl_arc = impl_def(db, parent_target.clone());
                    let impl_info_opt = impl_arc.as_ref().as_ref();

                    if let Some(impl_info) = impl_info_opt {
                        // Apply reverse map for user-facing type variable names
                        let impl_ty = display_ty(db, def_id, &impl_info.implementing_type);
                        let display_preds = display_predicates(db, def_id, &impl_info.predicates);

                        if let Some(ref trait_ty) = impl_info.trait_ty {
                            // Trait impl method: impl Trait[Type] where ..., fn sig
                            let display_trait_ty = display_ty(db, def_id, trait_ty);
                            signatures.push(format_impl_sig(
                                &impl_ty,
                                Some(&display_trait_ty),
                                &display_preds,
                            ));
                        } else {
                            // Inherent impl method: impl object Type where ..., fn sig
                            signatures.push(format_impl_sig(&impl_ty, None, &display_preds));
                        }
                    }

                    let parent_root = parent_header.as_ref().unwrap().root_node;
                    let sig_str = if let Some(parent_node) =
                        find_def_ast(&parse_result.ast.decls, parent_root)
                    {
                        find_method_in_parent(db, def_id, parent_node, impl_info_opt)
                    } else {
                        None
                    };
                    signatures.push(
                        sig_str
                            .unwrap_or_else(|| format_func_from_scheme(db, &target, &header.name)),
                    );
                }
                Some(DefKind::Trait) => {
                    // Trait method declaration: trait Name[ty_params], fn sig
                    // Use AST for user-facing type params
                    let parent_root = parent_header.as_ref().unwrap().root_node;
                    let parent_ast = find_def_ast(&parse_result.ast.decls, parent_root);
                    let trait_sig_str = parent_ast.and_then(|node| match &node.value {
                        Decl::Trait(tr) => Some(format!("trait {}", tr.ty)),
                        _ => None,
                    });
                    if let Some(sig) = trait_sig_str {
                        signatures.push(sig);
                    } else {
                        let parent_target = DefTarget::Workspace(parent_def_id);
                        if let Some(trait_info) = trait_def(db, parent_target) {
                            signatures
                                .push(format_trait_sig(&trait_info.path, &trait_info.type_params));
                        }
                    }

                    let sig_str =
                        parent_ast.and_then(|node| find_method_in_parent(db, def_id, node, None));
                    signatures.push(
                        sig_str
                            .unwrap_or_else(|| format_func_from_scheme(db, &target, &header.name)),
                    );
                }
                _ => {
                    // Fallback: just show the method signature
                    let sig_str = if let Some(node) = ast_node {
                        format_func_from_ast(db, def_id, node, None)
                    } else {
                        format_func_from_scheme(db, &target, &header.name)
                    };
                    signatures.push(sig_str);
                }
            }
        }

        DefKind::Struct => {
            // Struct: [module_path], struct Name[ty_params]
            if let Some(ref path) = item_path {
                if !path.module.is_empty() {
                    signatures.push(path.module.to_string());
                }
            }

            // Use AST type params for user-facing names
            let ty_params_str = ast_node
                .and_then(|node| match &node.value {
                    Decl::Struct(s) => s.ty_params.as_ref().map(|tp| tp.to_string()),
                    _ => None,
                })
                .unwrap_or_default();
            signatures.push(format!("struct {}{}", header.name, ty_params_str));
        }

        DefKind::StructField => {
            // Struct field: struct ParentName[ty_params], field: type
            if let Some(parent_def_id) = header.parent {
                let parent_target = DefTarget::Workspace(parent_def_id);
                let parent_header = def_header(db, parent_def_id);
                let parent_name = parent_header
                    .as_ref()
                    .map(|h| h.name.clone())
                    .unwrap_or_else(|| "?".to_string());

                let parent_ty_params = parent_header
                    .as_ref()
                    .and_then(|ph| {
                        let parent_parse = parse_file(db, parent_def_id.file);
                        find_def_ast(&parent_parse.ast.decls, ph.root_node).and_then(|node| {
                            match &node.value {
                                Decl::Struct(s) => s.ty_params.as_ref().map(|tp| tp.to_string()),
                                _ => None,
                            }
                        })
                    })
                    .unwrap_or_default();

                signatures.push(format!("struct {}{}", parent_name, parent_ty_params));

                let field_ty_str = struct_def(db, parent_target)
                    .and_then(|sdef| {
                        sdef.fields
                            .iter()
                            .find(|f| f.name == header.name)
                            .map(|field| display_ty(db, def_id, &field.ty.ty).to_string())
                    })
                    .unwrap_or_else(|| "?".to_string());
                signatures.push(format!("{}: {}", header.name, field_ty_str));
            } else {
                signatures.push(format!("{}: ?", header.name));
            }
        }

        DefKind::Trait => {
            // Trait: [module_path], trait Name[ty_params]
            if let Some(ref path) = item_path {
                if !path.module.is_empty() {
                    signatures.push(path.module.to_string());
                }
            }

            // Use AST type info for user-facing names
            let trait_ty_str = ast_node.and_then(|node| match &node.value {
                Decl::Trait(tr) => Some(tr.ty.to_string()),
                _ => None,
            });

            if let Some(ty_str) = trait_ty_str {
                signatures.push(format!("trait {}", ty_str));
            } else {
                let trait_target = DefTarget::Workspace(def_id);
                if let Some(tdef) = trait_def(db, trait_target) {
                    signatures.push(format_trait_sig(&tdef.path, &tdef.type_params));
                } else {
                    signatures.push(format!("trait {}", header.name));
                }
            }
        }

        DefKind::TypeAlias => {
            // Type alias: typealias Name[ty_params] = AliasedType
            // For now, just show the name; we could look up TypeAliasDef later
            let scheme = def_scheme(db, target);
            if let Some(scheme) = scheme {
                let vars = format_ty_vars(&scheme.vars);
                signatures.push(format!("typealias {}{} = {}", header.name, vars, scheme.ty));
            } else {
                signatures.push(format!("typealias {}", header.name));
            }
        }

        DefKind::Impl => {
            // Impl block: impl Trait['a, 'b, ...] or impl object Type
            let impl_target = DefTarget::Workspace(def_id);
            if let Some(impl_info) = impl_def(db, impl_target).as_ref() {
                let impl_ty = display_ty(db, def_id, &impl_info.implementing_type);
                let trait_display_ty = impl_info
                    .trait_ty
                    .as_ref()
                    .map(|ty| display_ty(db, def_id, ty));
                let display_preds = display_predicates(db, def_id, &impl_info.predicates);
                signatures.push(format_impl_sig(
                    &impl_ty,
                    trait_display_ty.as_ref(),
                    &display_preds,
                ));
            } else {
                signatures.push(format!("impl {}", header.name));
            }
        }

        DefKind::Binding { .. } => {
            // Local binding: name: type
            let scheme = def_scheme(db, target);
            let ty_str = scheme
                .map(|s| s.ty.to_string())
                .unwrap_or_else(|| "?".to_string());
            signatures.push(format!("{}: {}", header.name, ty_str));
        }

        DefKind::AssociatedConst { .. } => {
            // Associated constant: name: type
            let scheme = def_scheme(db, target);
            let ty_str = scheme
                .map(|s| s.ty.to_string())
                .unwrap_or_else(|| "?".to_string());
            signatures.push(format!("{}: {}", header.name, ty_str));
        }

        DefKind::FileMain | DefKind::Primitive => {
            // No meaningful display for these
            return None;
        }

        DefKind::Function { .. } => {
            // Function with parent (shouldn't happen, but handle gracefully)
            let sig_str = if let Some(node) = ast_node {
                format_func_from_ast(db, def_id, node, None)
            } else {
                format_func_from_scheme(db, &target, &header.name)
            };
            signatures.push(sig_str);
        }

        DefKind::Method => {
            // Method without parent (shouldn't happen, handled above)
            let sig_str = format_func_from_scheme(db, &target, &header.name);
            signatures.push(sig_str);
        }
    }

    if signatures.is_empty() {
        return None;
    }

    Some(DefDisplayInfo { signatures, doc })
}

fn library_display_info(db: &Database, target: &DefTarget) -> Option<DefDisplayInfo> {
    let path = def_path(db, target.clone())?;
    let scheme = get_display_scheme(db, target);

    let mut signatures = Vec::new();

    // Show the module path if present
    if !path.module.is_empty() {
        signatures.push(path.module.to_string());
    }

    // Format based on available type info
    if let Some(scheme) = scheme {
        let name = path.item_name().unwrap_or("?");
        match &scheme.ty {
            Ty::Func(_, _) => {
                signatures.push(format_func_from_scheme_data(name, &scheme));
            }
            _ => {
                signatures.push(format!("{}: {}", name, scheme.ty));
            }
        }
    } else {
        // No type info, just show the path
        signatures.push(path.to_string());
    }

    Some(DefDisplayInfo {
        signatures,
        doc: None,
    })
}

/// Format a function signature from an AST node containing a Decl.
///
/// When `parent_impl` is provided, inherited type vars and qualifiers are
/// stripped from the method signature.
fn format_func_from_ast(
    db: &Database,
    def_id: DefId,
    node: &Node<Decl>,
    parent_impl: Option<&ImplDef>,
) -> String {
    let target = DefTarget::Workspace(def_id);

    match &node.value {
        Decl::Func(func) => format_func_sig(db, &target, &func.sig, parent_impl),
        Decl::FnSig(sig) => format_func_sig(db, &target, sig, parent_impl),
        _ => format_func_from_scheme(db, &target, "?"),
    }
}

/// Find a method AST within a parent impl/trait node and format it.
fn find_method_in_parent(
    db: &Database,
    method_def_id: DefId,
    parent_node: &Node<Decl>,
    parent_impl: Option<&ImplDef>,
) -> Option<String> {
    let header = def_header(db, method_def_id)?;
    let root_node = header.root_node;

    match &parent_node.value {
        Decl::Impl(im) => {
            if let Some(funcs) = &im.funcs {
                for func_node in funcs {
                    if func_node.id == root_node {
                        return Some(format_func_from_ast(
                            db,
                            method_def_id,
                            func_node,
                            parent_impl,
                        ));
                    }
                }
            }
            if let Some(externs) = &im.externs {
                for ext_node in externs {
                    if ext_node.id == root_node {
                        return Some(format_func_from_ast(
                            db,
                            method_def_id,
                            ext_node,
                            parent_impl,
                        ));
                    }
                }
            }
        }
        Decl::Trait(tr) => {
            for field_node in &tr.fields {
                if field_node.id == root_node {
                    return Some(format_func_from_ast(db, method_def_id, field_node, None));
                }
            }
        }
        _ => {}
    }
    None
}

/// Format a function signature by combining AST info (modifiers, param names)
/// with type system info (resolved types).
///
/// Uses `def_scheme` for resolved types, then applies `mapped_def_types.reverse_map`
/// to substitute internal type variable names (like `?s:...`) with user-facing
/// names (like `'a`).
///
/// When `parent_impl` is provided, type vars and qualifiers inherited from the
/// parent impl block are stripped from the method signature (they are already
/// shown on the impl line).
fn format_func_sig(
    db: &Database,
    target: &DefTarget,
    sig: &FuncSig,
    parent_impl: Option<&ImplDef>,
) -> String {
    let scheme = get_display_scheme(db, target);

    let mut parts = Vec::new();

    // Modifiers
    for m in &sig.modifiers {
        parts.push(m.to_string());
    }

    // fn keyword
    parts.push("fn".to_string());

    let name = sig.path.name().unwrap_or_else(|| "__anon__".to_string());

    // Build the type params, params, and return type from the scheme
    if let Some(ref scheme) = scheme {
        // Strip parent impl vars and qualifiers from the method scheme
        let (vars, qualifiers) = if let Some(impl_info) = parent_impl {
            let parent_vars: Vec<_> = impl_info.type_params.iter().collect();
            let filtered_vars: Vec<_> = scheme
                .vars
                .iter()
                .filter(|v| !parent_vars.contains(v))
                .cloned()
                .collect();
            let parent_qual_strs: Vec<_> =
                impl_info.predicates.iter().map(|p| p.to_string()).collect();
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
        let (params_str, ret_str) = format_func_ty_parts(sig, &scheme.ty);
        let quals_str = format_qualifiers(&qualifiers);

        let sig_str = format!("{}{}{}{}", name, vars_str, params_str, ret_str);
        parts.push(sig_str);

        if !quals_str.is_empty() {
            return format!("{} where {}", parts.join(" "), quals_str);
        }
    } else {
        // No scheme available, use AST info only
        parts.push(sig.to_string());
    }

    parts.join(" ")
}

/// Format a function signature from a TyScheme without AST info.
fn format_func_from_scheme(db: &Database, target: &DefTarget, name: &str) -> String {
    let scheme = get_display_scheme(db, target);
    if let Some(scheme) = scheme {
        format_func_from_scheme_data(name, &scheme)
    } else {
        format!("fn {}", name)
    }
}

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
        DefTarget::Primitive(_) => None,
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
fn build_rename_subst(reverse_map: &HashMap<TyVar, TyVar>) -> Subst {
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

/// Apply the reverse variable mapping to a list of predicates for display.
fn display_predicates(db: &Database, owner: DefId, predicates: &[Predicate]) -> Vec<Predicate> {
    let reverse_map = collect_reverse_map(db, owner);
    if reverse_map.is_empty() {
        return predicates.to_vec();
    }
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

/// Format a function signature from scheme data.
fn format_func_from_scheme_data(name: &str, scheme: &TyScheme) -> String {
    let vars_str = format_ty_vars(&scheme.vars);
    let quals_str = format_qualifiers(&scheme.qualifiers);

    let sig = match &scheme.ty {
        Ty::Func(params, ret) => {
            let params_str = params
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            format!("fn {}{}({}) -> {}", name, vars_str, params_str, ret)
        }
        ty => format!("fn {}{}: {}", name, vars_str, ty),
    };

    if quals_str.is_empty() {
        sig
    } else {
        format!("{} where {}", sig, quals_str)
    }
}

/// Format function params and return type from AST param names + Ty::Func.
fn format_func_ty_parts(sig: &FuncSig, ty: &Ty) -> (String, String) {
    match ty {
        Ty::Func(param_tys, ret_ty) => {
            let params: Vec<String> = sig
                .params
                .iter()
                .zip(param_tys.iter())
                .map(|(param, ty)| {
                    let name = param.value.name().to_short_name();
                    if name == "self" {
                        // Show `self: Type` when the type is informative (e.g. a type variable)
                        let ty_str = ty.to_string();
                        if ty_str == "self" {
                            "self".to_string()
                        } else {
                            format!("self: {}", ty)
                        }
                    } else {
                        format!("{}: {}", name, ty)
                    }
                })
                .collect();

            // If there are more types than params (shouldn't happen, but handle it)
            let extra: Vec<String> = param_tys
                .iter()
                .skip(sig.params.len())
                .map(|ty| ty.to_string())
                .collect();

            let mut all_params = params;
            all_params.extend(extra);

            let params_str = format!("({})", all_params.join(", "));
            let ret_str = format!(" -> {}", ret_ty);

            (params_str, ret_str)
        }
        _ => {
            // Non-function type, use AST Display
            (
                format!(
                    "({})",
                    sig.params
                        .iter()
                        .map(|p| p.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                String::new(),
            )
        }
    }
}

/// Format type variables as `[var1, var2]`, or empty string if none.
fn format_ty_vars(vars: &[TyVar]) -> String {
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
fn format_qualifiers(qualifiers: &[Predicate]) -> String {
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

/// Format a trait signature: `trait Name[ty_params]`
fn format_trait_sig(path: &ItemPath, type_params: &[TyVar]) -> String {
    let name = path.item_name().unwrap_or("?");
    let vars = format_ty_vars(type_params);
    format!("trait {}{}", name, vars)
}

/// Format an impl signature, including where-clause predicates if any.
fn format_impl_sig(
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

/// Extract a doc comment from a declaration.
fn extract_doc_comment(decl: &Decl) -> Option<String> {
    match decl {
        Decl::Func(func) => func.sig.doc_comment.clone(),
        Decl::FnSig(sig) => sig.doc_comment.clone(),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        file_id::FileId,
        pathlib::{FilePath, ItemPath, ModulePath},
        resolution::DefTarget,
    };

    use crate::{
        queries::{
            display::def_display_info,
            libraries::LoadedLibraries,
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

    // Note: Local bindings (e.g. `x = 42` inside a function) are handled
    // separately in the hover handler via Resolution::Local + ty_of,
    // not through def_display_info. The DefKind::Binding path in
    // def_display_info covers top-level named declarations that appear
    // as DefHeaders (e.g. parameters with explicit names in module scope).

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
}

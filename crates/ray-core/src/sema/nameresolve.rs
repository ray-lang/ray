use std::collections::{HashMap, HashSet};
use std::ops::DerefMut;

use ray_shared::{
    collections::{namecontext::NameContext, nametree::Scope},
    def::DefId,
    local_binding::LocalBindingId,
    node_id::NodeId,
    pathlib::{ModulePath, Path},
    resolution::{DefTarget, NameKind, Resolution},
    span::{Sourced, parsed::Parsed},
    ty::{Ty, TyVar},
    type_param_id::TypeParamId,
};
use ray_typing::types::TyScheme;

use crate::{
    ast::{
        Assign, BinOp, Block, Boxed, Call, Cast, Closure, Curly, CurlyElement, Decl, Deref, Dict,
        Dot, Expr, Extern, File, FnParam, For, Func, FuncSig, If, Impl, Index, List, Literal, Loop,
        Module, Name, New, Node, Pattern, Range, Ref, ScopedAccess, Sequence, Set, Struct, Trait,
        Tuple, UnaryOp, WalkItem, WalkScopeKind, While, walk_file,
    },
    errors::{RayError, RayErrorKind, RayResult},
    sourcemap::SourceMap,
};

pub struct ResolveContext<'a> {
    imports: &'a HashMap<String, ModulePath>,
    exports: &'a HashMap<String, DefTarget>,
    import_exports: &'a dyn Fn(&str) -> Option<HashMap<String, DefTarget>>,
    current_def: Option<DefId>,
    local_counter: u32,
    local_scopes: Vec<HashMap<String, LocalBindingId>>,
    /// Stack of type parameter scopes (impl, trait, function can all introduce type params)
    type_param_scopes: Vec<HashMap<String, TypeParamId>>,
    resolutions: HashMap<NodeId, Resolution>,
    /// NodeIds of FnSig decls that have been resolved by their parent (trait/extern)
    /// to avoid re-processing when walked as standalone items
    resolved_fnsigs: HashSet<NodeId>,
}

impl<'a> ResolveContext<'a> {
    fn new(
        imports: &'a HashMap<String, ModulePath>,
        exports: &'a HashMap<String, DefTarget>,
        import_exports: &'a dyn Fn(&str) -> Option<HashMap<String, DefTarget>>,
    ) -> ResolveContext<'a> {
        ResolveContext {
            imports,
            exports,
            import_exports,
            current_def: None,
            local_counter: 0,
            local_scopes: Vec::new(),
            type_param_scopes: Vec::new(),
            resolutions: HashMap::new(),
            resolved_fnsigs: HashSet::new(),
        }
    }

    fn lookup_local(&self, name: &str) -> Option<LocalBindingId> {
        for scope in self.local_scopes.iter().rev() {
            if let Some(&local_id) = scope.get(name) {
                return Some(local_id);
            }
        }
        None
    }

    fn bind_local(&mut self, node_id: NodeId, name: String) {
        debug_assert!(self.current_def.is_some());
        let Some(owner_def_id) = self.current_def else {
            return;
        };

        // Skip if this node already has a resolution (e.g., it was already
        // resolved as an lvalue through a parent Index pattern)
        if self.resolutions.contains_key(&node_id) {
            return;
        }

        let local_id = LocalBindingId::new(owner_def_id, self.local_counter);
        self.local_counter += 1;
        if let Some(scope) = self.local_scopes.last_mut() {
            scope.insert(name, local_id);
        }
        self.resolutions
            .insert(node_id, Resolution::Local(local_id));
    }

    fn bind_locals(&mut self, iter: impl Iterator<Item = (NodeId, String)>) {
        for (node_id, name) in iter {
            self.bind_local(node_id, name);
        }
    }

    /// Returns combined type parameters from all scopes (impl, trait, function).
    /// Inner scopes shadow outer scopes.
    fn type_params(&self) -> HashMap<String, TypeParamId> {
        let mut combined = HashMap::new();
        for scope in &self.type_param_scopes {
            combined.extend(scope.clone());
        }
        combined
    }
}

/// Resolve names in a file AST and return the resolution table.
///
/// This is a pure function that walks the AST read-only and returns a mapping
/// from NodeIds to their resolutions without mutating the input.
///
/// Parameters:
/// - `ast`: The parsed file AST
/// - `imports`: Map from import alias to module path. For `import std::io`,
///   the key is "io" and the value is the module path.
/// - `exports`: Combined exports visible to this file (module exports, sibling exports,
///   and selective imports, already merged with correct priority)
/// - `import_exports`: Callback to get exports for an imported module by alias
pub fn resolve_names_in_file(
    ast: &File,
    imports: &HashMap<String, ModulePath>,
    exports: &HashMap<String, DefTarget>,
    import_exports: impl Fn(&str) -> Option<HashMap<String, DefTarget>>,
) -> HashMap<NodeId, Resolution> {
    let mut ctx = ResolveContext::new(imports, exports, &import_exports);

    for item in walk_file(ast) {
        match item {
            WalkItem::EnterScope(WalkScopeKind::FileMain) => {
                ctx.local_scopes.push(HashMap::new());
            }
            WalkItem::EnterScope(WalkScopeKind::Function) => {
                ctx.local_scopes.push(HashMap::new());
            }
            WalkItem::EnterScope(WalkScopeKind::Closure | WalkScopeKind::Block) => {
                ctx.local_scopes.push(HashMap::new());
            }
            WalkItem::EnterScope(WalkScopeKind::Impl | WalkScopeKind::Trait) => {
                // Type params are pushed when we see the Decl, not on EnterScope
            }
            WalkItem::ExitScope(WalkScopeKind::FileMain) => {
                // Don't pop FileMain's scope - its locals should remain visible
                // to sibling declarations (functions, etc.) in the same file.
            }
            WalkItem::ExitScope(WalkScopeKind::Function) => {
                ctx.local_scopes.pop();
                ctx.type_param_scopes.pop();
            }
            WalkItem::ExitScope(WalkScopeKind::Impl)
            | WalkItem::ExitScope(WalkScopeKind::Trait) => {
                ctx.type_param_scopes.pop();
            }
            WalkItem::ExitScope(WalkScopeKind::Block | WalkScopeKind::Closure) => {
                ctx.local_scopes.pop();
            }
            WalkItem::Decl(decl) => {
                resolve_names_in_decl(decl, &mut ctx);
            }
            WalkItem::Func(func) => {
                // This is emitted for impl methods.
                ctx.current_def = Some(func.id.owner);
                ctx.local_counter = 0;

                // Bind function parameters
                resolve_names_in_func_params(&func.sig, &mut ctx);
            }
            WalkItem::Expr(expr) => {
                match &expr.value {
                    Expr::Name(name) => {
                        let name_str = name.path.name().unwrap_or_default();
                        // Check locals first
                        let resolution = ctx
                            .lookup_local(&name_str)
                            .map(Resolution::Local)
                            .or_else(|| exports.get(&name_str).cloned().map(Resolution::Def));
                        if let Some(res) = resolution {
                            ctx.resolutions.insert(expr.id, res);
                        }
                    }
                    Expr::Path(path) if path.len() == 1 => {
                        let name_str = path.name().unwrap_or_default();
                        let resolution = ctx
                            .lookup_local(&name_str)
                            .map(Resolution::Local)
                            .or_else(|| exports.get(&name_str).cloned().map(Resolution::Def));
                        if let Some(res) = resolution {
                            ctx.resolutions.insert(expr.id, res);
                        }
                    }
                    Expr::Path(path) if path.len() >= 2 => {
                        // Qualified path like `io::read` or `std::io::read`
                        // Try to resolve via imports first
                        let name_vec = path.to_name_vec();
                        let first_segment = name_vec.first().cloned().unwrap_or_default();
                        if imports.contains_key(&first_segment) {
                            // Look up the exports for this import alias
                            if let Some(imported_exports) = import_exports(&first_segment) {
                                // For now, only handle two-segment paths like `io::read`
                                if path.len() == 2 {
                                    let second_segment =
                                        name_vec.get(1).cloned().unwrap_or_default();
                                    if let Some(target) = imported_exports.get(&second_segment) {
                                        ctx.resolutions
                                            .insert(expr.id, Resolution::Def(target.clone()));
                                    }
                                }
                            }
                        }
                    }
                    Expr::Closure(closure) => {
                        // Bind closure parameters
                        ctx.bind_locals(closure.args.items.iter().filter_map(|arg| {
                            let Expr::Name(name) = &arg.value else {
                                return None;
                            };

                            let Some(name) = name.path.name() else {
                                return None;
                            };

                            Some((arg.id, name))
                        }));
                    }
                    Expr::Curly(curly) => {
                        // Resolve the struct type name for curly expressions like `Point { x, y }`
                        // The resolution is stored on the Curly expression's NodeId
                        if let Some(parsed_path) = &curly.lhs {
                            if let Some(name_str) = parsed_path.name() {
                                // Look up the struct in exports
                                if let Some(target) = exports.get(&name_str).cloned() {
                                    ctx.resolutions.insert(expr.id, Resolution::Def(target));
                                }
                            }
                        }
                    }
                    Expr::Cast(cast) => {
                        // Resolve type references in cast expressions (e.g., `x as int`)
                        let type_params = ctx.type_params();
                        collect_type_resolutions(&cast.ty, &type_params, &mut ctx);
                    }
                    Expr::New(new_expr) => {
                        // Resolve type references in new expressions (e.g., `new(Point, 10)`)
                        let type_params = ctx.type_params();
                        collect_type_resolutions(&new_expr.ty.value, &type_params, &mut ctx);
                    }
                    Expr::Type(parsed_ty_scheme) => {
                        // Resolve type references in type expressions (e.g., `sizeof(int)`)
                        let type_params = ctx.type_params();
                        collect_type_resolutions_from_scheme(
                            parsed_ty_scheme,
                            &type_params,
                            &mut ctx,
                        );
                    }
                    _ => {}
                }
            }
            WalkItem::Pattern(pat) => {
                // Handle assignment patterns - create new bindings for new names,
                // resolve existing bindings for lvalues
                for node in pat.paths().into_iter() {
                    let (path, is_lvalue) = node.value;
                    let Some(name) = path.name() else {
                        continue;
                    };

                    if is_lvalue {
                        // For lvalues (e.g., `l` in `l[0] = 42`), look up the existing
                        // binding and record a resolution without creating a new binding
                        if let Some(local_id) = ctx.lookup_local(&name) {
                            ctx.resolutions.insert(node.id, Resolution::Local(local_id));
                        }
                    } else {
                        // For new bindings, create and bind
                        ctx.bind_local(node.id, name);
                    }
                }
            }
            // Curly element shorthand (e.g., `Point { x }` where `x` is both field name and value).
            // The walker doesn't descend into CurlyElement::Name because the inner Name isn't
            // wrapped in a Node (it's just `Name`, not `Node<Name>`). We handle it explicitly
            // here so the shorthand resolves to the local variable being referenced.
            // For CurlyElement::Labeled, the walker descends into the value expression normally.
            WalkItem::CurlyElement(elem) => {
                if let CurlyElement::Name(name) = &elem.value {
                    let name_str = name.path.name().unwrap_or_default();
                    let resolution = ctx
                        .lookup_local(&name_str)
                        .map(Resolution::Local)
                        .or_else(|| exports.get(&name_str).cloned().map(Resolution::Def));
                    if let Some(res) = resolution {
                        ctx.resolutions.insert(elem.id, res);
                    }
                }
            }
            _ => {}
        }
    }

    ctx.resolutions
}

fn resolve_names_in_decl(decl: &Node<Decl>, ctx: &mut ResolveContext<'_>) {
    match &decl.value {
        Decl::Extern(_ext) => {
            // The walker automatically visits the inner decl (ext.decl_node()),
            // and FnSig handles its own type params via sig.ty_params, so we
            // don't need to do anything special here.
        }
        Decl::Func(func) => {
            ctx.current_def = Some(decl.id.owner);
            ctx.local_counter = 0;

            // Push function's type params for expressions in the body
            let ty_vars = extract_ty_vars_from_type_params(&func.sig.ty_params);
            let scope = build_type_param_scope(decl.id.owner, &ty_vars);
            ctx.type_param_scopes.push(scope);

            resolve_names_in_func_sig(decl.id.owner, &func.sig, ctx);
        }
        Decl::FnSig(sig) => {
            // Skip if already resolved by parent (trait method or extern function)
            // to avoid overwriting resolutions that were done with parent's type params
            if ctx.resolved_fnsigs.contains(&decl.id) {
                return;
            }
            ctx.current_def = Some(decl.id.owner);
            ctx.local_counter = 0;
            // FnSig has no body, so no type param scope needed for expressions.
            // The signature's type refs are resolved in resolve_names_in_func_sig.
            resolve_names_in_func_sig(decl.id.owner, sig, ctx);
        }
        Decl::Struct(struct_decl) => {
            // Resolve type references in struct field types
            resolve_struct_type_refs(decl.id.owner, struct_decl, ctx);
        }
        Decl::Trait(trait_decl) => {
            // Push trait's type params for method signatures
            let ty_vars = trait_decl.ty.value().type_params();
            let scope = build_type_param_scope(decl.id.owner, &ty_vars);
            ctx.type_param_scopes.push(scope);

            // Resolve type references in trait definition
            resolve_trait_type_refs(decl.id.owner, trait_decl, ctx);
        }
        Decl::Impl(imp) => {
            // Push impl's type params for method bodies
            let ty_vars = imp.ty.value().type_params();
            let scope = build_type_param_scope(decl.id.owner, &ty_vars);
            ctx.type_param_scopes.push(scope);

            // Resolve type references in impl block
            resolve_impl_type_refs(decl.id.owner, imp, ctx);
        }
        Decl::TypeAlias(_name, aliased_ty) => {
            // Resolve type references in type alias
            resolve_type_alias_type_refs(aliased_ty, ctx);
        }
        Decl::Mutable(name_node) | Decl::Name(name_node) => {
            // Resolve type annotation in binding declaration (e.g., `x: Int` or `mut x: String`)
            if let Some(parsed_ty_scheme) = &name_node.value.ty {
                // Bindings don't have type parameters
                let type_params = HashMap::new();
                collect_type_resolutions_from_scheme(parsed_ty_scheme, &type_params, ctx);
            }
        }
        Decl::Declare(assign) => {
            // Resolve type annotation in assignment with declaration (e.g., `x: Int = 5`)
            if let Pattern::Name(name) = &assign.lhs.value {
                if let Some(parsed_ty_scheme) = &name.ty {
                    // Bindings don't have type parameters
                    let type_params = HashMap::new();
                    collect_type_resolutions_from_scheme(parsed_ty_scheme, &type_params, ctx);
                }
            }
        }
        Decl::FileMain(_stmts) => {
            // Set up FileMain as the current definition owner for local bindings.
            // FileMain always has DefId with index 0 for the file.
            ctx.current_def = Some(decl.id.owner);
            ctx.local_counter = 0;
        }
    }
}

fn resolve_names_in_func_sig(owner_def_id: DefId, sig: &FuncSig, ctx: &mut ResolveContext<'_>) {
    // Bind function parameters
    resolve_names_in_func_params(sig, ctx);

    // Resolve type references in function signature
    resolve_func_type_refs(owner_def_id, sig, ctx);
}

fn resolve_names_in_func_params(sig: &FuncSig, ctx: &mut ResolveContext<'_>) {
    ctx.bind_locals(sig.params.iter().filter_map(|param| {
        if let Some(name) = param.name().name() {
            Some((param.id, name))
        } else {
            None
        }
    }))
}

/// Resolve type references in a struct definition.
///
/// For `struct Foo['a] { x: 'a, y: Bar }`, this resolves:
/// - Type parameter `'a` in field `x` to TypeParam
/// - Type `Bar` in field `y` to its definition
fn resolve_struct_type_refs(def_id: DefId, struct_decl: &Struct, ctx: &mut ResolveContext<'_>) {
    // Build type parameter scope from struct's type params
    let ty_vars = extract_ty_vars_from_type_params(&struct_decl.ty_params);
    let type_params = build_type_param_scope(def_id, &ty_vars);

    // Resolve each field type
    if let Some(fields) = &struct_decl.fields {
        for field in fields {
            if let Some(parsed_ty_scheme) = &field.value.ty {
                collect_type_resolutions_from_scheme(parsed_ty_scheme, &type_params, ctx);
            }
        }
    }
}

/// Resolve type references in a trait definition.
///
/// For `trait Eq['a] extends Hash['a] { fn eq(self, other: 'a): bool }`, this resolves:
/// - Super trait `Hash['a]` type references
/// - Method signature type references (parameters, return types, qualifiers)
///
/// Type parameters from the trait (e.g., `'a`) are in scope for all resolutions.
fn resolve_trait_type_refs(def_id: DefId, trait_decl: &Trait, ctx: &mut ResolveContext<'_>) {
    // Build type parameter scope from trait's type (e.g., Eq['a] -> {'a: TypeParamId})
    let ty_vars = trait_decl.ty.value().type_params();
    let type_params = build_type_param_scope(def_id, &ty_vars);

    // Resolve super trait if present
    if let Some(super_trait) = &trait_decl.super_trait {
        collect_type_resolutions(super_trait, &type_params, ctx);
    }

    // Resolve method signatures and mark them as resolved so the walker
    // doesn't re-process them without the trait's type params in scope
    for field in &trait_decl.fields {
        if let Decl::FnSig(sig) = &field.value {
            resolve_func_sig(
                field.id.owner,
                sig,
                &type_params, // Trait's type params are in scope
                ctx,
            );
            // Mark this FnSig as already resolved
            ctx.resolved_fnsigs.insert(field.id);
        }
    }
}

/// Resolve type references in an impl block.
///
/// For `impl ToStr[Point]`, this resolves:
/// - The trait type `ToStr`
/// - The implementing type `Point`
/// - All nested type arguments (e.g., `impl Trait[Dict[K, V]]` resolves K, V too)
/// - Method signatures (parameters, return types, qualifiers)
///
/// For `impl object Point`, resolves the implementing type and methods.
fn resolve_impl_type_refs(def_id: DefId, imp: &Impl, ctx: &mut ResolveContext<'_>) {
    // Build type parameter scope from impl's type (e.g., impl Eq['a] -> {'a: TypeParamId})
    // For most impls like `impl ToStr[Point]`, there are no type params at impl level
    let ty_vars = imp.ty.value().type_params();
    let type_params = build_type_param_scope(def_id, &ty_vars);

    // Resolve the impl type (trait and implementing type) with ALL nested type args
    // This handles cases like `impl Trait[Dict[K, V]]` where K, V need resolution
    collect_type_resolutions(&imp.ty, &type_params, ctx);

    // Resolve qualifiers (where clause)
    for qualifier in &imp.qualifiers {
        collect_type_resolutions(qualifier, &type_params, ctx);
    }

    // Resolve method signatures
    if let Some(funcs) = &imp.funcs {
        for decl in funcs {
            let Decl::Func(func) = &decl.value else {
                unreachable!("impl funcs should only contain Decl::Func");
            };
            resolve_func_sig(
                decl.id.owner,
                &func.sig,
                &type_params, // Impl's type params are in scope for methods
                ctx,
            );
        }
    }
}

/// Resolve type references in a top-level function definition.
///
/// For `fn foo['a](x: 'a, y: Bar): List['a]`, this resolves:
/// - Type parameters to their TypeParamIds
/// - Parameter types (e.g., `Bar` to its definition)
/// - Return type (e.g., `List` to its definition)
/// - Qualifier/where-clause types
fn resolve_func_type_refs(def_id: DefId, sig: &FuncSig, ctx: &mut ResolveContext<'_>) {
    // Build type parameter scope from function's type params
    let ty_vars = extract_ty_vars_from_type_params(&sig.ty_params);
    let type_params = build_type_param_scope(def_id, &ty_vars);

    // Use resolve_func_sig to handle the signature resolution
    resolve_func_sig(def_id, &sig, &type_params, ctx);
}

/// Resolve type references in a type alias definition.
///
/// For `typealias MyList = List[Int]`, this resolves types in the aliased type
/// (e.g., `List`, `Int`) to their definitions.
///
/// Note: typealias doesn't have type variables on the LHS. Any type variables
/// in the aliased type (e.g., `'a` in `List['a]`) are free/unbound and will
/// resolve to Error since there's no declaration site for them.
fn resolve_type_alias_type_refs(aliased_ty: &Parsed<Ty>, ctx: &mut ResolveContext<'_>) {
    // Type aliases don't have bound type parameters - any type variables
    // in the aliased type are free/unbound
    let type_params = HashMap::new();

    // Resolve the aliased type
    collect_type_resolutions(aliased_ty, &type_params, ctx);
}

/// Extract the type name from a Ty for name resolution.
///
/// For Ty::Var, returns the variable name (e.g., "'a").
/// For Ty::Const/Ty::Proj, returns the item name from the path.
/// For structural types (Func, Ref, etc.), returns None.
fn extract_type_name(ty: &Ty) -> Option<String> {
    match ty {
        Ty::Var(ty_var) => ty_var.path().name(),
        _ => ty
            .item_path()
            .and_then(|p| p.item_name())
            .map(|s| s.to_string()),
    }
}

/// Build a type parameter scope from a list of type variables.
///
/// Maps each type variable name (e.g., "'a", "'b") to a TypeParamId
/// with the given owner DefId and sequential indices.
pub fn build_type_param_scope(owner: DefId, params: &[TyVar]) -> HashMap<String, TypeParamId> {
    params
        .iter()
        .enumerate()
        .filter_map(|(idx, ty_var)| {
            ty_var.path().name().map(|name| {
                (
                    name,
                    TypeParamId {
                        owner,
                        index: idx as u32,
                    },
                )
            })
        })
        .collect()
}

/// Extract type variables from TypeParams.
///
/// TypeParams contains `Vec<Parsed<Ty>>` where each Ty should be a `Ty::Var`.
/// This extracts the TyVar from each.
fn extract_ty_vars_from_type_params(ty_params: &Option<crate::ast::TypeParams>) -> Vec<TyVar> {
    ty_params
        .as_ref()
        .map(|tp| {
            tp.tys
                .iter()
                .filter_map(|parsed_ty| {
                    if let Ty::Var(ty_var) = parsed_ty.value() {
                        Some(ty_var.clone())
                    } else {
                        None
                    }
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Resolve type references in a function signature.
///
/// Resolves:
/// - Parameter types (from `FnParam.parsed_ty()`)
/// - Return type (`FuncSig.ret_ty`)
/// - Qualifier/where-clause types (`FuncSig.qualifiers`)
///
/// The method's own type parameters are combined with parent type parameters
/// to form the complete scope for resolution.
pub fn resolve_func_sig(
    method_def_id: DefId,
    sig: &FuncSig,
    parent_type_params: &HashMap<String, TypeParamId>,
    ctx: &mut ResolveContext<'_>,
) {
    // Method may have its own type parameters
    let mut type_params = parent_type_params.clone();
    let method_ty_vars = extract_ty_vars_from_type_params(&sig.ty_params);
    let method_params = build_type_param_scope(method_def_id, &method_ty_vars);
    type_params.extend(method_params);

    // Resolve parameter types
    for param in &sig.params {
        if let Some(parsed_ty_scheme) = param.value.parsed_ty() {
            collect_type_resolutions_from_scheme(parsed_ty_scheme, &type_params, ctx);
        }
    }

    // Resolve return type
    if let Some(parsed_ty) = &sig.ret_ty {
        collect_type_resolutions(parsed_ty, &type_params, ctx);
    }

    // Resolve where clause / qualifiers
    for qualifier in &sig.qualifiers {
        collect_type_resolutions(qualifier, &type_params, ctx);
    }
}

/// Resolves all type references in a Parsed<TyScheme> using its synthetic IDs.
///
/// Similar to collect_type_resolutions but works with TyScheme which wraps a Ty.
pub fn collect_type_resolutions_from_scheme(
    parsed_ty_scheme: &Parsed<TyScheme>,
    type_params: &HashMap<String, TypeParamId>,
    ctx: &mut ResolveContext<'_>,
) {
    let synthetic_ids = parsed_ty_scheme.synthetic_ids();
    let ty_refs = parsed_ty_scheme.value().mono().flatten();

    // The synthetic_ids should match the flattened type refs
    // If they don't match, we skip resolution (this can happen for empty types)
    if synthetic_ids.len() != ty_refs.len() {
        return;
    }

    for (node_id, ty) in synthetic_ids.iter().zip(ty_refs.iter()) {
        // Only resolve named types, skip structural types (Func, Ref, etc.)
        if let Some(name) = extract_type_name(ty) {
            let resolution = resolve_type_name(&name, type_params, ctx);
            ctx.resolutions.insert(*node_id, resolution);
        }
    }
}

/// Resolve a type name to a Resolution.
///
/// Checks in order:
/// 1. Type parameters in scope (e.g., `'a`, `'b`)
/// 2. Imports (direct imports)
/// 3. Module exports (same-module definitions)
/// 4. Imported module exports (qualified imports)
fn resolve_type_name(
    name: &str,
    type_params: &HashMap<String, TypeParamId>,
    ctx: &mut ResolveContext<'_>,
) -> Resolution {
    // 1. Check if it's a type parameter in scope
    if let Some(type_param_id) = type_params.get(name) {
        return Resolution::TypeParam(*type_param_id);
    }

    // 2. Check imports
    if let Some(module_path) = ctx.imports.get(name) {
        if let Some(exports) = (ctx.import_exports)(&module_path.to_string()) {
            if let Some(target) = exports.get(name) {
                return Resolution::Def(target.clone());
            }
        }
    }

    // 3. Check module exports (same-module definitions)
    if let Some(target) = ctx.exports.get(name) {
        return Resolution::Def(target.clone());
    }

    // 4. Check imported module exports (qualified imports)
    for (_alias, module_path) in ctx.imports {
        if let Some(exports) = (ctx.import_exports)(&module_path.to_string()) {
            if let Some(target) = exports.get(name) {
                return Resolution::Def(target.clone());
            }
        }
    }

    Resolution::Error {
        name: name.to_string(),
        kind: NameKind::Type,
    }
}

/// Resolves all type references in a Parsed<Ty> using its synthetic IDs.
///
/// The synthetic_ids in Parsed<Ty> correspond 1:1 with the flattened type refs.
/// For each type reference, we determine its resolution:
/// - Ty::Var (type parameters like 'a): look up in type_params map
/// - Ty::Const/Ty::Proj (nominal types): look up in imports/exports via resolve_type_name
///
/// The resolutions are inserted into the provided HashMap.
pub fn collect_type_resolutions(
    parsed_ty: &Parsed<Ty>,
    type_params: &HashMap<String, TypeParamId>,
    ctx: &mut ResolveContext<'_>,
) {
    let synthetic_ids = parsed_ty.synthetic_ids();
    let ty_refs = parsed_ty.value().flatten();

    assert_eq!(
        synthetic_ids.len(),
        ty_refs.len(),
        "Synthetic ID count must match flattened type ref count"
    );

    for (node_id, ty) in synthetic_ids.iter().zip(ty_refs.iter()) {
        // Only resolve named types, skip structural types (Func, Ref, etc.)
        if let Some(name) = extract_type_name(ty) {
            let resolution = resolve_type_name(&name, type_params, ctx);
            ctx.resolutions.insert(*node_id, resolution);
        }
    }
}

// ============================================================================
// Legacy name resolution (mutating AST)
// ============================================================================

pub struct LegacyResolveContext<'a> {
    ncx: &'a mut NameContext,
    srcmap: &'a SourceMap,
    scope_map: &'a HashMap<Path, Vec<Scope>>,
    scope_stack: Vec<Path>,
    /// Current definition being processed (for LocalBindingId.owner).
    current_def: Option<DefId>,
    /// Counter for local bindings within current def.
    local_counter: u32,
    /// Local bindings in scope: name -> LocalBindingId.
    local_scopes: Vec<HashMap<String, LocalBindingId>>,
    /// Output: NodeId -> Resolution mappings (produced as side-effect).
    resolutions: HashMap<NodeId, Resolution>,
}

impl<'a> LegacyResolveContext<'a> {
    pub fn new(
        ncx: &'a mut NameContext,
        srcmap: &'a mut SourceMap,
        scope_map: &'a HashMap<Path, Vec<Scope>>,
    ) -> Self {
        Self {
            ncx,
            srcmap,
            scope_map,
            scope_stack: Vec::new(),
            current_def: None,
            local_counter: 0,
            local_scopes: vec![HashMap::new()],
            resolutions: HashMap::new(),
        }
    }

    /// Enter a new definition scope (function, method).
    pub fn enter_def(&mut self, def_id: DefId) {
        self.current_def = Some(def_id);
        self.local_counter = 0;
        self.local_scopes.push(HashMap::new());
    }

    /// Exit a definition scope.
    pub fn exit_def(&mut self) {
        self.current_def = None;
        self.local_counter = 0;
        self.local_scopes.pop();
    }

    /// Allocate a new LocalBindingId for a binding definition.
    fn alloc_local(&mut self) -> Option<LocalBindingId> {
        let owner = self.current_def?;
        let id = LocalBindingId::new(owner, self.local_counter);
        self.local_counter += 1;
        Some(id)
    }

    /// Register a local binding by name and record its resolution.
    pub fn bind_local(&mut self, name: &str, node_id: NodeId) -> Option<LocalBindingId> {
        let local_id = self.alloc_local()?;
        if let Some(scope) = self.local_scopes.last_mut() {
            scope.insert(name.to_string(), local_id);
        }
        self.resolutions
            .insert(node_id, Resolution::Local(local_id));
        Some(local_id)
    }

    /// Look up a local binding by name.
    pub fn lookup_local(&self, name: &str) -> Option<LocalBindingId> {
        for scope in self.local_scopes.iter().rev() {
            if let Some(&local_id) = scope.get(name) {
                return Some(local_id);
            }
        }
        None
    }

    /// Record a resolution for a name reference node.
    pub fn record_resolution(&mut self, node_id: NodeId, resolution: Resolution) {
        self.resolutions.insert(node_id, resolution);
    }

    /// Get the resolution table.
    pub fn resolutions(&self) -> &HashMap<NodeId, Resolution> {
        &self.resolutions
    }

    /// Consume and return the resolution table.
    pub fn into_resolutions(self) -> HashMap<NodeId, Resolution> {
        self.resolutions
    }

    pub fn add_path(&mut self, path: &Path) {
        let fqn = path.to_name_vec();
        log::debug!("add_path: {:?}", fqn);
        self.ncx.nametree_mut().add_full_name(&fqn);
    }

    fn bind_local_name(&mut self, scope: &Path, name: &mut Path) {
        let full_path = scope.with_names_only().append_path(name.clone());
        log::debug!(
            "bind_local_name: scope={:?} name={} full_path={}",
            scope,
            name,
            full_path
        );
        *name = full_path.clone();
        self.add_path(&full_path);
    }

    fn push_scope_path(&mut self, scope: Path) {
        self.scope_stack.push(scope);
    }

    fn pop_scope_path(&mut self) {
        self.scope_stack.pop();
    }

    fn current_scope_or(&self, fallback: &Path) -> Path {
        self.scope_stack
            .last()
            .cloned()
            .unwrap_or_else(|| fallback.clone())
    }

    pub fn resolve_func_body(&mut self, def_id: DefId, func: &mut Func) -> RayResult<()> {
        if let Some(body) = &mut func.body {
            self.enter_def(def_id);
            self.push_scope_path(func.sig.path.value.with_names_only());

            for param in &mut func.sig.params {
                // Get the name string before mutating (FnParam.name() returns &Path)
                let name_str = param.value.name().name();
                // Mutate the path as before
                self.bind_local_name(&func.sig.path, param.name_mut());
                // Register the local binding with its NodeId
                if let Some(name) = name_str {
                    self.bind_local(&name, param.id);
                }
            }

            body.resolve_names(self)?;
            self.pop_scope_path();
            self.exit_def();
        }
        Ok(())
    }
}

pub trait NameResolve {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()>;
}

impl NameResolve for Sourced<'_, Name> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let src = self.src();
        let name = self.path.to_string();
        let mut scopes = ctx.scope_map.get(self.src_module()).unwrap().clone();
        for scope_path in ctx.scope_stack.iter() {
            scopes.push(Scope::from(scope_path.clone()));
        }
        if ctx.scope_stack.is_empty() {
            scopes.push(Scope::from(src.path.clone()));
        }
        match ctx.ncx.resolve_name(&scopes, &name) {
            Some(fqn) => {
                log::debug!("fqn for `{}`: {}", name, fqn);
                self.path = fqn.clone();
            }
            _ => {
                log::debug!("nametree: {:#?}", ctx.ncx.nametree());
                return Err(RayError {
                    msg: format!("`{}` is undefined", self),
                    src: vec![self.src().clone()],
                    kind: RayErrorKind::Name,
                    context: Some(format!("resolving name `{self}`")),
                });
            }
        }
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Path> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let mut scopes = ctx.scope_map.get(self.src_module()).unwrap().clone();
        for scope_path in ctx.scope_stack.iter() {
            scopes.push(Scope::from(scope_path.clone()));
        }
        if ctx.scope_stack.is_empty() {
            scopes.push(Scope::from(self.src().path.clone()));
        }
        log::debug!(
            "[Path::resolve_names] looking for name `{}` in scopes: {:?}",
            self,
            scopes
        );
        match ctx.ncx.resolve_path(&scopes, &self) {
            Some(fqn) => {
                log::debug!("fqn for `{}`: {}", self, fqn);
                *self.deref_mut() = fqn.clone();
            }
            _ => {
                log::debug!("nametree: {:?}", ctx.ncx.nametree());
                return Err(RayError {
                    msg: format!("`{}` is undefined", self),
                    src: vec![self.src().clone()],
                    kind: RayErrorKind::Name,
                    context: Some(format!("resolving name from path `{self}`")),
                });
            }
        }
        Ok(())
    }
}

impl NameResolve for Node<Decl> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        match &mut self.value {
            Decl::Extern(extern_) => Sourced(extern_, &src).resolve_names(ctx),
            Decl::Mutable(_) => todo!(),
            Decl::Name(_) => todo!(),
            Decl::Declare(declare) => Sourced(declare, &src).resolve_names(ctx),
            Decl::Func(func) => Sourced(func, &src).resolve_names(ctx),
            Decl::FnSig(fnsig) => Sourced(fnsig, &src).resolve_names(ctx),
            Decl::Struct(struct_) => Sourced(struct_, &src).resolve_names(ctx),
            Decl::Trait(trait_) => Sourced(trait_, &src).resolve_names(ctx),
            Decl::TypeAlias(_, _) => todo!(),
            Decl::Impl(impl_) => Sourced(impl_, &src).resolve_names(ctx),
            Decl::FileMain(stmts) => {
                for stmt in stmts {
                    stmt.resolve_names(ctx)?;
                }
                Ok(())
            }
        }
    }
}

impl NameResolve for Node<Expr> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        let node_id = self.id;

        // For Name and Path expressions, check for local bindings first
        match &mut self.value {
            Expr::Name(name) => {
                // Check if this is a local binding first
                let name_str = name.path.name().unwrap_or_default();
                if let Some(local_id) = ctx.lookup_local(&name_str) {
                    ctx.record_resolution(node_id, Resolution::Local(local_id));
                    return Ok(());
                }
                // Otherwise resolve as a definition (defer DefTarget recording for now)
                Sourced(name, &src).resolve_names(ctx)
            }
            Expr::Path(path) => {
                // Check if this is a local binding first (single-segment paths only)
                if path.len() == 1 {
                    let name_str = path.name().unwrap_or_default();
                    if let Some(local_id) = ctx.lookup_local(&name_str) {
                        ctx.record_resolution(node_id, Resolution::Local(local_id));
                        return Ok(());
                    }
                }
                // Otherwise resolve as a definition (defer DefTarget recording for now)
                Sourced(path, &src).resolve_names(ctx)
            }
            _ => Sourced(&mut self.value, &src).resolve_names(ctx),
        }
    }
}

impl NameResolve for Node<FnParam> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        match &mut self.value {
            FnParam::Name(name) => Sourced(name, &src).resolve_names(ctx),
            FnParam::DefaultValue(param, _) => Sourced(param, &src).resolve_names(ctx),
            FnParam::Missing { .. } => Ok(()),
        }
    }
}

impl<T> NameResolve for Option<T>
where
    T: NameResolve,
{
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        if let Some(value) = self {
            value.resolve_names(ctx)
        } else {
            Ok(())
        }
    }
}

impl<T> NameResolve for Box<T>
where
    T: NameResolve,
{
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.as_mut().resolve_names(ctx)
    }
}

impl<T> NameResolve for Vec<T>
where
    T: NameResolve,
{
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        for el in self {
            el.resolve_names(ctx)?;
        }

        Ok(())
    }
}

impl NameResolve for Module<(), Decl> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        // resolve names in each declaration in the module
        self.decls.resolve_names(ctx)?;

        // resolve names the declarations again but only process the bodies of functions
        for decl in self.decls.iter_mut() {
            let decl_def_id = decl.id.owner;
            match decl.deref_mut() {
                Decl::Func(func) => {
                    ctx.resolve_func_body(decl_def_id, func)?;
                }
                Decl::Impl(impl_) => {
                    if let Some(funcs) = &mut impl_.funcs {
                        for decl_node in funcs {
                            let func_def_id = decl_node.id.owner;
                            let Decl::Func(func) = &mut decl_node.value else {
                                unreachable!("impl funcs should only contain Decl::Func");
                            };
                            ctx.resolve_func_body(func_def_id, func)?;
                        }
                    }
                }
                _ => continue,
            }
        }

        Ok(())
    }
}

impl NameResolve for Sourced<'_, Extern> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let (ext, src) = self.unpack_mut();
        match ext.decl_mut() {
            Decl::Mutable(_) => todo!(),
            Decl::Name(_) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::FnSig(sig) => {
                log::debug!("NameResolve::resolve_names: extern fn sig: {:?}", sig);
                ctx.add_path(&sig.path);
            }
            Decl::Struct(struct_) => Sourced(struct_, src).resolve_names(ctx)?,
            Decl::Impl(impl_) => Sourced(impl_, src).resolve_names(ctx)?,
            Decl::Func(_)
            | Decl::Trait(_)
            | Decl::TypeAlias(_, _)
            | Decl::Extern(_)
            | Decl::FileMain(_) => {
                unreachable!("extern cannot wrap {:?}", ext.decl())
            }
        }

        Ok(())
    }
}

impl NameResolve for Sourced<'_, Func> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let (func, src) = self.unpack_mut();
        // note: we're only processing the signature here and not the body
        Sourced(&mut func.sig, src).resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, FuncSig> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let (sig, _) = self.unpack_mut();
        ctx.add_path(&sig.path);
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Struct> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let (st, _) = self.unpack_mut();
        let name = st.path.name().unwrap();
        if !Ty::is_builtin_name(&name) {
            ctx.add_path(&st.path);
        }

        Ok(())
    }
}

impl NameResolve for Sourced<'_, Trait> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let (tr, src) = self.unpack_mut();
        let trait_fqn = &src.path;
        ctx.ncx
            .nametree_mut()
            .add_full_name(&trait_fqn.to_name_vec());
        log::debug!("[Trait::resolve_names] {:?}", tr);
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Impl> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let (imp, src) = self.unpack_mut();
        if let Some(funcs) = &mut imp.funcs {
            for decl in funcs {
                let Decl::Func(func) = &mut decl.value else {
                    unreachable!("impl funcs should only contain Decl::Func");
                };
                log::debug!("resolve_names: impl func: {:?}", func.sig);
                Sourced(&mut func.sig, src).resolve_names(ctx)?;
            }
        }

        Ok(())
    }
}

impl NameResolve for Sourced<'_, Expr> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let (expr, src) = self.unpack_mut();
        match expr {
            Expr::Assign(a) => Sourced(a, src).resolve_names(ctx),
            Expr::BinOp(bin_op) => Sourced(bin_op, src).resolve_names(ctx),
            Expr::Block(block) => Sourced(block, src).resolve_names(ctx),
            Expr::Boxed(boxed) => Sourced(boxed, src).resolve_names(ctx),
            Expr::Break(break_) => Sourced(break_, src).resolve_names(ctx),
            Expr::Continue => Ok(()),
            Expr::Call(call) => Sourced(call, src).resolve_names(ctx),
            Expr::Cast(cast) => Sourced(cast, src).resolve_names(ctx),
            Expr::Closure(closure) => Sourced(closure, src).resolve_names(ctx),
            Expr::Curly(curly) => Sourced(curly, src).resolve_names(ctx),
            Expr::Dict(dict) => Sourced(dict, src).resolve_names(ctx),
            Expr::DefaultValue(default_value) => Sourced(default_value, src).resolve_names(ctx),
            Expr::Deref(deref) => Sourced(deref, src).resolve_names(ctx),
            Expr::Dot(dot) => Sourced(dot, src).resolve_names(ctx),
            Expr::Func(func) => Sourced(func, src).resolve_names(ctx),
            Expr::For(for_) => Sourced(for_, src).resolve_names(ctx),
            Expr::If(if_) => Sourced(if_, src).resolve_names(ctx),
            Expr::Index(index) => Sourced(index, src).resolve_names(ctx),
            Expr::Labeled(labeled, _) => Sourced(labeled, src).resolve_names(ctx),
            Expr::List(list) => Sourced(list, src).resolve_names(ctx),
            Expr::Literal(literal) => Sourced(literal, src).resolve_names(ctx),
            Expr::Loop(loop_) => Sourced(loop_, src).resolve_names(ctx),
            Expr::Name(name) => Sourced(name, src).resolve_names(ctx),
            Expr::New(new) => Sourced(new, src).resolve_names(ctx),
            Expr::Path(path) => Sourced(path, src).resolve_names(ctx),
            Expr::Pattern(pattern) => Sourced(pattern, src).resolve_names(ctx),
            Expr::Paren(paren) => Sourced(paren, src).resolve_names(ctx),
            Expr::Range(range) => Sourced(range, src).resolve_names(ctx),
            Expr::Ref(rf) => Sourced(rf, src).resolve_names(ctx),
            Expr::Return(return_) => Sourced(return_, src).resolve_names(ctx),
            Expr::Sequence(sequence) => Sourced(sequence, src).resolve_names(ctx),
            Expr::Set(set) => Sourced(set, src).resolve_names(ctx),
            Expr::ScopedAccess(scoped_access) => Sourced(scoped_access, src).resolve_names(ctx),
            Expr::Some(inner) => Sourced(inner, src).resolve_names(ctx),
            Expr::Tuple(tuple) => Sourced(tuple, src).resolve_names(ctx),
            Expr::Type(type_) => type_.resolve_names(ctx),
            Expr::TypeAnnotated(type_annotated, _) => {
                Sourced(type_annotated, src).resolve_names(ctx)
            }
            Expr::UnaryOp(unary_op) => Sourced(unary_op, src).resolve_names(ctx),
            Expr::Unsafe(unsafe_) => Sourced(unsafe_, src).resolve_names(ctx),
            Expr::While(while_) => Sourced(while_, src).resolve_names(ctx),
            Expr::Missing(_) => todo!("resolve_names: Expr::Missing: {:?}", expr),
        }
    }
}

impl NameResolve for Sourced<'_, ScopedAccess> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Assign> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let (assign, src) = self.unpack_mut();
        for node in assign.lhs.paths_mut() {
            let (path, is_lvalue) = node.value;
            let base_scope = ctx.current_scope_or(&src.path.with_names_only());
            let name_str = path.name();
            let full_path = base_scope.append_path(path.clone());
            *path = full_path.clone();

            if is_lvalue {
                // For lvalues (e.g., `l` in `l[0] = 42`), look up the existing
                // binding and record a resolution without creating a new binding
                if let Some(n) = name_str {
                    if let Some(local_id) = ctx.lookup_local(&n) {
                        ctx.record_resolution(node.id, Resolution::Local(local_id));
                    }
                }
            } else {
                ctx.add_path(&full_path);
                // Register the local binding with its NodeId
                if let Some(n) = name_str {
                    ctx.bind_local(&n, node.id);
                }
            }
        }

        assign.rhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, BinOp> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)?;
        self.rhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Block> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.stmts.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Boxed> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.inner.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Call> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.callee.resolve_names(ctx)?;
        self.args.items.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Cast> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Closure> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let (closure, src) = self.unpack_mut();
        let scope_suffix = format!("__closure_{:x}", closure.body.id);
        let closure_scope = src
            .path
            .with_names_only()
            .append_path(Path::from(scope_suffix));
        ctx.push_scope_path(closure_scope.clone());
        // Push a new local scope for the closure's parameters
        ctx.local_scopes.push(HashMap::new());

        for arg in closure.args.items.iter_mut() {
            let arg_src = ctx.srcmap.get(arg);
            let arg_node_id = arg.id;
            match &mut arg.value {
                Expr::Name(name) => {
                    // Get name string before mutating
                    let name_str = name.path.name();
                    ctx.bind_local_name(&closure_scope, &mut name.path);
                    // Register the local binding with its NodeId
                    if let Some(n) = name_str {
                        ctx.bind_local(&n, arg_node_id);
                    }
                }
                _ => {
                    return Err(RayError {
                        msg: format!(
                            "unsupported closure parameter `{}`; only simple names are allowed",
                            arg.value
                        ),
                        src: vec![arg_src],
                        kind: RayErrorKind::Parse,
                        context: Some("resolve closure parameters".to_string()),
                    });
                }
            }
        }

        closure.body.resolve_names(ctx)?;
        // Pop the local scope
        ctx.local_scopes.pop();
        ctx.pop_scope_path();
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Curly> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.elements.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Dict> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        for (key, value) in self.entries.iter_mut() {
            key.resolve_names(ctx)?;
            value.resolve_names(ctx)?;
        }
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Set> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.items.resolve_names(ctx)
    }
}

impl NameResolve for Node<CurlyElement> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        match &mut self.value {
            CurlyElement::Name(n) => Sourced(n, &src).resolve_names(ctx),
            CurlyElement::Labeled(_, rhs) => rhs.resolve_names(ctx),
        }
    }
}

impl NameResolve for Sourced<'_, Deref> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.expr.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Dot> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, For> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.expr.resolve_names(ctx)?;

        let scope_suffix = format!("__for_{:x}", self.body.id);
        let base_scope = ctx.current_scope_or(&self.src().path.with_names_only());
        let for_scope = base_scope.append_path(Path::from(scope_suffix));

        ctx.push_scope_path(for_scope.clone());
        ctx.local_scopes.push(HashMap::new());
        for node in self.pat.paths_mut() {
            let (path, is_lvalue) = node.value;
            if is_lvalue {
                continue;
            }
            let name_str = path.name();
            ctx.bind_local_name(&for_scope, path);
            if let Some(n) = name_str {
                ctx.bind_local(&n, node.id);
            }
        }
        self.body.resolve_names(ctx)?;
        ctx.local_scopes.pop();
        ctx.pop_scope_path();
        Ok(())
    }
}

impl NameResolve for Sourced<'_, If> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.cond.resolve_names(ctx)?;
        self.then.resolve_names(ctx)?;
        self.els.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Index> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)?;
        self.index.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, List> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.items.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Literal> {
    fn resolve_names(&mut self, _: &mut LegacyResolveContext) -> RayResult<()> {
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Loop> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.body.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, New> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        if let Some(count) = &mut self.count {
            count.resolve_names(ctx)?
        }
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Pattern> {
    fn resolve_names(&mut self, _: &mut LegacyResolveContext) -> RayResult<()> {
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Range> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.start.resolve_names(ctx)?;
        self.end.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Ref> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.expr.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Sequence> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.items.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Tuple> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.seq.items.resolve_names(ctx)
    }
}

impl NameResolve for Parsed<TyScheme> {
    fn resolve_names(&mut self, _: &mut LegacyResolveContext) -> RayResult<()> {
        Ok(())
    }
}

impl NameResolve for Sourced<'_, UnaryOp> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.expr.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, While> {
    fn resolve_names(&mut self, ctx: &mut LegacyResolveContext) -> RayResult<()> {
        self.cond.resolve_names(ctx)?;
        self.body.resolve_names(ctx)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        def::DefId,
        file_id::FileId,
        node_id::NodeId,
        pathlib::{FilePath, Path},
        resolution::{DefTarget, NameKind, Resolution},
        span::{Source, Span, parsed::Parsed},
        ty::{Ty, TyVar},
        type_param_id::TypeParamId,
    };
    use ray_typing::types::TyScheme;

    use ray_typing::types::NominalKind;

    use crate::{
        ast::{
            Assign, Block, Cast, Closure as AstClosure, Curly, CurlyElement, Decl, Expr, Extern,
            File, FnParam, Func, FuncSig, Impl, Literal, Name, New, Node, Pattern as AstPattern,
            ScopedAccess, Sequence, Struct, Trait, TypeParams,
            token::{Token, TokenKind},
        },
        sema::{
            build_type_param_scope, collect_type_resolutions, nameresolve::ResolveContext,
            resolve_func_sig, resolve_names_in_file,
        },
    };

    fn test_file(decls: Vec<Node<Decl>>, stmts: Vec<Node<Expr>>) -> File {
        File {
            path: Path::from("test"),
            stmts,
            decls,
            imports: vec![],
            doc_comment: None,
            filepath: FilePath::from("test.ray"),
            span: Span::new(),
        }
    }

    #[test]
    fn resolve_names_in_file_resolves_function_parameter() {
        // fn f(x) { x }
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        let param = Node::new(crate::ast::FnParam::Name(Name::new("x")));
        let body_name = Node::new(Expr::Name(Name::new("x")));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![body_name.clone()],
        }));
        let func = Func::new(
            Node::new(Path::from("test::f")),
            vec![param.clone()],
            func_body,
        );
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Parameter should be resolved
        assert!(resolutions.contains_key(&param.id));
        let param_res = resolutions.get(&param.id).unwrap();
        assert!(matches!(param_res, Resolution::Local(_)));

        // Body name should resolve to the parameter
        assert!(resolutions.contains_key(&body_name.id));
        let body_res = resolutions.get(&body_name.id).unwrap();
        assert!(matches!(body_res, Resolution::Local(_)));

        // Both should resolve to the same LocalBindingId
        assert_eq!(param_res, body_res);
    }

    #[test]
    fn resolve_names_in_file_resolves_module_export() {
        // fn f() { foo }  where foo is in module_exports
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        let body_name = Node::new(Expr::Name(Name::new("foo")));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![body_name.clone()],
        }));
        let func = Func::new(Node::new(Path::from("test::f")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let foo_def_id = DefId::new(FileId(0), 1);
        exports.insert("foo".to_string(), DefTarget::Workspace(foo_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Body name should resolve to the export
        assert!(resolutions.contains_key(&body_name.id));
        let body_res = resolutions.get(&body_name.id).unwrap();
        assert!(matches!(body_res, Resolution::Def(DefTarget::Workspace(id)) if *id == foo_def_id));
    }

    #[test]
    fn resolve_names_in_file_resolves_export() {
        // fn f() { bar }  where bar is in exports
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        let body_name = Node::new(Expr::Name(Name::new("bar")));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![body_name.clone()],
        }));
        let func = Func::new(Node::new(Path::from("test::f")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let bar_def_id = DefId::new(FileId(0), 2);
        exports.insert("bar".to_string(), DefTarget::Workspace(bar_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Body name should resolve to the export
        assert!(resolutions.contains_key(&body_name.id));
        let body_res = resolutions.get(&body_name.id).unwrap();
        assert!(matches!(body_res, Resolution::Def(DefTarget::Workspace(id)) if *id == bar_def_id));
    }

    #[test]
    fn resolve_names_in_file_local_shadows_export() {
        // fn f(x) { x }  where x is also in module_exports - local should win
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        let param = Node::new(crate::ast::FnParam::Name(Name::new("x")));
        let body_name = Node::new(Expr::Name(Name::new("x")));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![body_name.clone()],
        }));
        let func = Func::new(
            Node::new(Path::from("test::f")),
            vec![param.clone()],
            func_body,
        );
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let x_def_id = DefId::new(FileId(0), 1);
        exports.insert("x".to_string(), DefTarget::Workspace(x_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Body name should resolve to local, not export
        assert!(resolutions.contains_key(&body_name.id));
        let body_res = resolutions.get(&body_name.id).unwrap();
        assert!(matches!(body_res, Resolution::Local(_)));
    }

    #[test]
    fn resolve_names_in_file_let_binding() {
        // fn f() { y = 1; y }
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        let local_pattern = Node::new(AstPattern::Name(Name::new("y")));
        let rhs_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let assign = Assign {
            lhs: local_pattern.clone(),
            rhs: Box::new(rhs_expr),
            is_mut: false,
            mut_span: None,
            op: crate::ast::InfixOp::Assign,
            op_span: Span::new(),
        };
        let assign_expr = Node::new(Expr::Assign(assign));
        let body_name = Node::new(Expr::Name(Name::new("y")));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![assign_expr, body_name.clone()],
        }));
        let func = Func::new(Node::new(Path::from("test::f")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // The pattern node should have a resolution
        let pattern_paths = local_pattern.paths();
        assert!(!pattern_paths.is_empty());
        let pattern_node_id = pattern_paths[0].id;
        assert!(resolutions.contains_key(&pattern_node_id));

        // Body name should resolve to local
        assert!(resolutions.contains_key(&body_name.id));
        let body_res = resolutions.get(&body_name.id).unwrap();
        assert!(matches!(body_res, Resolution::Local(_)));
    }

    #[test]
    fn resolve_names_in_file_closure_parameter() {
        // fn f() { |z| z }
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        let closure_arg = Node::new(Expr::Name(Name::new("z")));
        let closure_body = Node::new(Expr::Name(Name::new("z")));
        let closure = AstClosure {
            args: Sequence::new(vec![closure_arg.clone()]),
            body: Box::new(closure_body.clone()),
            arrow_span: None,
            curly_spans: None,
        };
        let closure_expr = Node::new(Expr::Closure(closure));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![closure_expr],
        }));
        let func = Func::new(Node::new(Path::from("test::f")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Closure arg should be resolved
        assert!(resolutions.contains_key(&closure_arg.id));
        let arg_res = resolutions.get(&closure_arg.id).unwrap();
        assert!(matches!(arg_res, Resolution::Local(_)));

        // Closure body should resolve to the argument
        assert!(resolutions.contains_key(&closure_body.id));
        let body_res = resolutions.get(&closure_body.id).unwrap();
        assert!(matches!(body_res, Resolution::Local(_)));

        // Both should be the same local
        assert_eq!(arg_res, body_res);
    }

    #[test]
    fn resolve_names_in_file_unresolved_name_not_in_map() {
        // fn f() { unknown }  where unknown is nowhere
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        let body_name = Node::new(Expr::Name(Name::new("unknown")));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![body_name.clone()],
        }));
        let func = Func::new(Node::new(Path::from("test::f")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Unknown name should not be in the resolution map
        assert!(!resolutions.contains_key(&body_name.id));
    }

    #[test]
    fn resolve_names_in_file_resolves_curly_struct_type() {
        // fn f() { Point { x: 1 } }  where Point is a struct export
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create curly expression: Point { x: 1 }
        let field_name = Name::new("x");
        let field_value = Node::new(Expr::Name(Name::new("dummy")));
        let curly_elem = Node::new(CurlyElement::Labeled(field_name, field_value));
        let curly_expr = Node::new(Expr::Curly(Curly {
            lhs: Some(Parsed::new(Path::from("Point"), Source::default())),
            elements: vec![curly_elem],
            curly_span: Span::default(),
            ty: TyScheme::default(),
        }));
        let curly_id = curly_expr.id;

        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![curly_expr],
        }));
        let func = Func::new(Node::new(Path::from("test::f")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();

        // Point is exported from the module
        let point_def_id = DefId::new(FileId(0), 1);
        let mut exports = HashMap::new();
        exports.insert("Point".to_string(), DefTarget::Workspace(point_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Curly expression should be resolved to the Point struct
        assert!(
            resolutions.contains_key(&curly_id),
            "Curly expression should have resolution"
        );
        assert_eq!(
            resolutions.get(&curly_id),
            Some(&Resolution::Def(DefTarget::Workspace(point_def_id))),
            "Curly should resolve to Point struct"
        );
    }

    // =========================================================================
    // Tests for collect_type_resolutions
    // =========================================================================

    #[test]
    fn collect_type_resolutions_resolves_simple_type_to_export() {
        // Type annotation: Point
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create a Parsed<Ty> with a synthetic ID
        let ty = Ty::con("Point");
        let node_id = NodeId::new();
        let mut parsed_ty = Parsed::new(ty, Source::default());
        parsed_ty.set_synthetic_ids(vec![node_id]);

        // Set up exports
        let point_def_id = DefId::new(FileId(0), 1);
        let mut exports = HashMap::new();
        exports.insert("Point".to_string(), DefTarget::Workspace(point_def_id));

        let type_params = HashMap::new();
        let imports = HashMap::new();
        let mut ctx = ResolveContext::new(&imports, &exports, &|_| None);

        collect_type_resolutions(&parsed_ty, &type_params, &mut ctx);

        assert_eq!(
            ctx.resolutions.get(&node_id),
            Some(&Resolution::Def(DefTarget::Workspace(point_def_id))),
            "Simple type should resolve to export"
        );
    }

    #[test]
    fn collect_type_resolutions_resolves_generic_type_with_type_param() {
        // Type annotation: List['a] where List is a struct and 'a is a type parameter
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create List['a] - the type variable is Ty::Var
        let ty = Ty::proj("List", vec![Ty::var("'a")]);
        let list_node_id = NodeId::new();
        let a_node_id = NodeId::new();
        let mut parsed_ty = Parsed::new(ty, Source::default());
        parsed_ty.set_synthetic_ids(vec![list_node_id, a_node_id]);

        // Set up exports for List
        let list_def_id = DefId::new(FileId(0), 1);
        let mut exports = HashMap::new();
        exports.insert("List".to_string(), DefTarget::Workspace(list_def_id));

        // Set up type_params for 'a
        let mut type_params = HashMap::new();
        let a_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        type_params.insert("'a".to_string(), a_type_param_id);

        let imports = HashMap::new();
        let mut ctx = ResolveContext::new(&imports, &exports, &|_| None);

        collect_type_resolutions(&parsed_ty, &type_params, &mut ctx);

        // List should be resolved to the export
        assert_eq!(
            ctx.resolutions.get(&list_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(list_def_id))),
            "List should resolve to export"
        );
        // 'a should be resolved to the type parameter
        assert_eq!(
            ctx.resolutions.get(&a_node_id),
            Some(&Resolution::TypeParam(a_type_param_id)),
            "Type parameter 'a should resolve to TypeParam"
        );
    }

    #[test]
    fn collect_type_resolutions_unresolved_returns_error() {
        // Type annotation: Unknown (not in scope)
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        let ty = Ty::con("Unknown");
        let node_id = NodeId::new();
        let mut parsed_ty = Parsed::new(ty, Source::default());
        parsed_ty.set_synthetic_ids(vec![node_id]);

        let type_params = HashMap::new();
        let exports = HashMap::new();
        let imports = HashMap::new();
        let mut ctx = ResolveContext::new(&imports, &exports, &|_| None);

        collect_type_resolutions(&parsed_ty, &type_params, &mut ctx);

        assert_eq!(
            ctx.resolutions.get(&node_id),
            Some(&Resolution::Error {
                name: "Unknown".to_string(),
                kind: NameKind::Type,
            }),
            "Unknown type should resolve to Error"
        );
    }

    #[test]
    fn collect_type_resolutions_nested_generic_types() {
        // Type annotation: Dict[String, Int] where Dict, String, Int are all structs
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        let ty = Ty::proj("Dict", vec![Ty::con("String"), Ty::con("Int")]);
        let dict_node_id = NodeId::new();
        let string_node_id = NodeId::new();
        let int_node_id = NodeId::new();
        let mut parsed_ty = Parsed::new(ty, Source::default());
        parsed_ty.set_synthetic_ids(vec![dict_node_id, string_node_id, int_node_id]);

        // Set up exports
        let dict_def_id = DefId::new(FileId(0), 1);
        let string_def_id = DefId::new(FileId(0), 2);
        let int_def_id = DefId::new(FileId(0), 3);
        let mut exports = HashMap::new();
        exports.insert("Dict".to_string(), DefTarget::Workspace(dict_def_id));
        exports.insert("String".to_string(), DefTarget::Workspace(string_def_id));
        exports.insert("Int".to_string(), DefTarget::Workspace(int_def_id));

        let type_params = HashMap::new();
        let imports = HashMap::new();
        let mut ctx = ResolveContext::new(&imports, &exports, &|_| None);

        collect_type_resolutions(&parsed_ty, &type_params, &mut ctx);

        assert_eq!(
            ctx.resolutions.get(&dict_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(dict_def_id))),
            "Dict should resolve to export"
        );
        assert_eq!(
            ctx.resolutions.get(&string_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(string_def_id))),
            "String should resolve to export"
        );
        assert_eq!(
            ctx.resolutions.get(&int_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(int_def_id))),
            "Int should resolve to export"
        );
    }

    // =========================================================================
    // Tests for build_type_param_scope
    // =========================================================================

    #[test]
    fn build_type_param_scope_empty_params() {
        let def_id = DefId::new(FileId(0), 0);
        let params: Vec<TyVar> = vec![];

        let scope = build_type_param_scope(def_id, &params);

        assert!(scope.is_empty(), "Empty params should produce empty scope");
    }

    #[test]
    fn build_type_param_scope_single_param() {
        let def_id = DefId::new(FileId(0), 0);
        let params = vec![TyVar::new("'a")];

        let scope = build_type_param_scope(def_id, &params);

        assert_eq!(scope.len(), 1);
        assert_eq!(
            scope.get("'a"),
            Some(&TypeParamId {
                owner: def_id,
                index: 0
            })
        );
    }

    #[test]
    fn build_type_param_scope_multiple_params() {
        let def_id = DefId::new(FileId(0), 0);
        let params = vec![TyVar::new("'a"), TyVar::new("'b"), TyVar::new("'c")];

        let scope = build_type_param_scope(def_id, &params);

        assert_eq!(scope.len(), 3);
        assert_eq!(
            scope.get("'a"),
            Some(&TypeParamId {
                owner: def_id,
                index: 0
            })
        );
        assert_eq!(
            scope.get("'b"),
            Some(&TypeParamId {
                owner: def_id,
                index: 1
            })
        );
        assert_eq!(
            scope.get("'c"),
            Some(&TypeParamId {
                owner: def_id,
                index: 2
            })
        );
    }

    #[test]
    fn build_type_param_scope_preserves_owner() {
        let def_id_1 = DefId::new(FileId(0), 1);
        let def_id_2 = DefId::new(FileId(1), 2);
        let params = vec![TyVar::new("'x")];

        let scope_1 = build_type_param_scope(def_id_1, &params);
        let scope_2 = build_type_param_scope(def_id_2, &params);

        assert_eq!(scope_1.get("'x").unwrap().owner, def_id_1);
        assert_eq!(scope_2.get("'x").unwrap().owner, def_id_2);
    }

    // =========================================================================
    // Tests for resolve_func_sig
    // =========================================================================

    fn make_func_sig(path: &str) -> FuncSig {
        FuncSig {
            path: Node::new(Path::from(path)),
            params: vec![],
            ty_params: None,
            ret_ty: None,
            ty: None,
            modifiers: vec![],
            qualifiers: vec![],
            doc_comment: None,
            is_anon: false,
            is_method: false,
            has_body: true,
            span: Span::default(),
        }
    }

    #[test]
    fn resolve_func_sig_empty_signature() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        let sig = make_func_sig("test::f");
        let parent_type_params = HashMap::new();
        let imports = HashMap::new();
        let exports = HashMap::new();
        let mut ctx = ResolveContext::new(&imports, &exports, &|_| None);

        resolve_func_sig(def_id, &sig, &parent_type_params, &mut ctx);

        // Empty signature should produce no resolutions
        assert!(ctx.resolutions.is_empty());
    }

    #[test]
    fn resolve_func_sig_resolves_return_type() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create a return type: Point
        let ret_ty = Ty::con("Point");
        let ret_node_id = NodeId::new();
        let mut parsed_ret_ty = Parsed::new(ret_ty, Source::default());
        parsed_ret_ty.set_synthetic_ids(vec![ret_node_id]);

        let mut sig = make_func_sig("test::f");
        sig.ret_ty = Some(parsed_ret_ty);

        // Set up exports for Point
        let point_def_id = DefId::new(FileId(0), 1);
        let mut exports = HashMap::new();
        exports.insert("Point".to_string(), DefTarget::Workspace(point_def_id));

        let parent_type_params = HashMap::new();
        let imports = HashMap::new();
        let mut ctx = ResolveContext::new(&imports, &exports, &|_| None);

        resolve_func_sig(def_id, &sig, &parent_type_params, &mut ctx);

        assert_eq!(
            ctx.resolutions.get(&ret_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(point_def_id))),
            "Return type should resolve to export"
        );
    }

    #[test]
    fn resolve_func_sig_resolves_qualifier() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create a qualifier: ToStr['a]
        let qualifier_ty = Ty::proj("ToStr", vec![Ty::var("'a")]);
        let tostr_node_id = NodeId::new();
        let a_node_id = NodeId::new();
        let mut parsed_qualifier = Parsed::new(qualifier_ty, Source::default());
        parsed_qualifier.set_synthetic_ids(vec![tostr_node_id, a_node_id]);

        let mut sig = make_func_sig("test::f");
        sig.qualifiers = vec![parsed_qualifier];

        // Set up exports for ToStr
        let tostr_def_id = DefId::new(FileId(0), 1);
        let mut exports = HashMap::new();
        exports.insert("ToStr".to_string(), DefTarget::Workspace(tostr_def_id));

        // Set up parent type params for 'a
        let mut parent_type_params = HashMap::new();
        let a_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        parent_type_params.insert("'a".to_string(), a_type_param_id);

        let imports = HashMap::new();
        let mut ctx = ResolveContext::new(&imports, &exports, &|_| None);

        resolve_func_sig(def_id, &sig, &parent_type_params, &mut ctx);

        assert_eq!(
            ctx.resolutions.get(&tostr_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(tostr_def_id))),
            "Qualifier trait should resolve to export"
        );
        assert_eq!(
            ctx.resolutions.get(&a_node_id),
            Some(&Resolution::TypeParam(a_type_param_id)),
            "Type parameter in qualifier should resolve to parent type param"
        );
    }

    #[test]
    fn resolve_func_sig_resolves_param_type() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create a parameter with type annotation: x: Point
        let param_ty = Ty::con("Point");
        let param_node_id = NodeId::new();
        let mut parsed_ty_scheme = Parsed::new(TyScheme::from(param_ty), Source::default());
        parsed_ty_scheme.set_synthetic_ids(vec![param_node_id]);

        let mut name = Name::new("x");
        name.ty = Some(parsed_ty_scheme);
        let param = Node::new(FnParam::Name(name));

        let mut sig = make_func_sig("test::f");
        sig.params = vec![param];

        // Set up exports for Point
        let point_def_id = DefId::new(FileId(0), 1);
        let mut exports = HashMap::new();
        exports.insert("Point".to_string(), DefTarget::Workspace(point_def_id));

        let parent_type_params = HashMap::new();
        let imports = HashMap::new();
        let mut ctx = ResolveContext::new(&imports, &exports, &|_| None);

        resolve_func_sig(def_id, &sig, &parent_type_params, &mut ctx);

        assert_eq!(
            ctx.resolutions.get(&param_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(point_def_id))),
            "Parameter type should resolve to export"
        );
    }

    // =========================================================================
    // Tests for resolve_names_in_file with struct definitions
    // =========================================================================

    #[test]
    fn resolve_names_in_file_resolves_struct_field_type() {
        // struct Foo { x: Bar }
        // where Bar is a struct in exports
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create a field with type annotation: x: Bar
        let field_ty = Ty::con("Bar");
        let field_node_id = NodeId::new();
        let mut parsed_ty_scheme = Parsed::new(TyScheme::from(field_ty), Source::default());
        parsed_ty_scheme.set_synthetic_ids(vec![field_node_id]);

        let mut field_name = Name::new("x");
        field_name.ty = Some(parsed_ty_scheme);
        let field = Node::new(field_name);

        // Create struct declaration
        let struct_decl = Struct {
            kind: NominalKind::Struct,
            path: Node::new(Path::from("test::Foo")),
            ty_params: None,
            fields: Some(vec![field]),
        };
        let decl = Node::new(Decl::Struct(struct_decl));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let bar_def_id = DefId::new(FileId(0), 1);
        exports.insert("Bar".to_string(), DefTarget::Workspace(bar_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Field type should resolve to Bar
        assert_eq!(
            resolutions.get(&field_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(bar_def_id))),
            "Field type Bar should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_struct_field_with_type_param() {
        // struct Foo['a] { x: 'a }
        // Type parameter 'a should resolve to TypeParam
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create a field with type annotation: x: 'a
        let field_ty = Ty::var("'a");
        let field_node_id = NodeId::new();
        let mut parsed_ty_scheme = Parsed::new(TyScheme::from(field_ty), Source::default());
        parsed_ty_scheme.set_synthetic_ids(vec![field_node_id]);

        let mut field_name = Name::new("x");
        field_name.ty = Some(parsed_ty_scheme);
        let field = Node::new(field_name);

        // Create type parameter 'a
        let ty_param = Ty::var("'a");
        let ty_param_parsed = Parsed::new(ty_param, Source::default());

        // Create struct declaration with type parameter
        let struct_decl = Struct {
            kind: NominalKind::Struct,
            path: Node::new(Path::from("test::Foo")),
            ty_params: Some(TypeParams {
                tys: vec![ty_param_parsed],
                lb_span: Span::default(),
                rb_span: Span::default(),
            }),
            fields: Some(vec![field]),
        };
        let decl = Node::new(Decl::Struct(struct_decl));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Field type should resolve to TypeParam
        let expected_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        assert_eq!(
            resolutions.get(&field_node_id),
            Some(&Resolution::TypeParam(expected_type_param_id)),
            "Field type 'a should resolve to TypeParam"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_struct_generic_field_type() {
        // struct Foo['a] { x: List['a] }
        // List should resolve to export, 'a should resolve to TypeParam
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create a field with type annotation: x: List['a]
        let field_ty = Ty::proj("List", vec![Ty::var("'a")]);
        let list_node_id = NodeId::new();
        let a_node_id = NodeId::new();
        let mut parsed_ty_scheme = Parsed::new(TyScheme::from(field_ty), Source::default());
        parsed_ty_scheme.set_synthetic_ids(vec![list_node_id, a_node_id]);

        let mut field_name = Name::new("x");
        field_name.ty = Some(parsed_ty_scheme);
        let field = Node::new(field_name);

        // Create type parameter 'a
        let ty_param = Ty::var("'a");
        let ty_param_parsed = Parsed::new(ty_param, Source::default());

        // Create struct declaration with type parameter
        let struct_decl = Struct {
            kind: NominalKind::Struct,
            path: Node::new(Path::from("test::Foo")),
            ty_params: Some(TypeParams {
                tys: vec![ty_param_parsed],
                lb_span: Span::default(),
                rb_span: Span::default(),
            }),
            fields: Some(vec![field]),
        };
        let decl = Node::new(Decl::Struct(struct_decl));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let list_def_id = DefId::new(FileId(0), 1);
        exports.insert("List".to_string(), DefTarget::Workspace(list_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // List should resolve to export
        assert_eq!(
            resolutions.get(&list_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(list_def_id))),
            "List should resolve to export"
        );

        // 'a should resolve to TypeParam
        let expected_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        assert_eq!(
            resolutions.get(&a_node_id),
            Some(&Resolution::TypeParam(expected_type_param_id)),
            "Type parameter 'a should resolve to TypeParam"
        );
    }

    #[test]
    fn resolve_names_in_file_struct_unresolved_field_type() {
        // struct Foo { x: Unknown }
        // Unknown is not in scope, should resolve to Error
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create a field with type annotation: x: Unknown
        let field_ty = Ty::con("Unknown");
        let field_node_id = NodeId::new();
        let mut parsed_ty_scheme = Parsed::new(TyScheme::from(field_ty), Source::default());
        parsed_ty_scheme.set_synthetic_ids(vec![field_node_id]);

        let mut field_name = Name::new("x");
        field_name.ty = Some(parsed_ty_scheme);
        let field = Node::new(field_name);

        // Create struct declaration
        let struct_decl = Struct {
            kind: NominalKind::Struct,
            path: Node::new(Path::from("test::Foo")),
            ty_params: None,
            fields: Some(vec![field]),
        };
        let decl = Node::new(Decl::Struct(struct_decl));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let exports = HashMap::new(); // Unknown is not in exports

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Field type should resolve to Error
        assert_eq!(
            resolutions.get(&field_node_id),
            Some(&Resolution::Error {
                name: "Unknown".to_string(),
                kind: NameKind::Type,
            }),
            "Unknown type should resolve to Error"
        );
    }

    // =========================================================================
    // Tests for resolve_names_in_file with trait definitions
    // =========================================================================

    #[test]
    fn resolve_names_in_file_resolves_trait_super_trait() {
        // trait Eq['a] extends Hash['a]
        // Hash should resolve to export, 'a should resolve to TypeParam
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create super trait type: Hash['a]
        let super_trait_ty = Ty::proj("Hash", vec![Ty::var("'a")]);
        let hash_node_id = NodeId::new();
        let a_node_id = NodeId::new();
        let mut parsed_super_trait = Parsed::new(super_trait_ty, Source::default());
        parsed_super_trait.set_synthetic_ids(vec![hash_node_id, a_node_id]);

        // Create trait type: Eq['a]
        let trait_ty = Ty::proj("Eq", vec![Ty::var("'a")]);
        let parsed_trait_ty = Parsed::new(trait_ty, Source::default());

        // Create trait declaration
        let trait_decl = Trait {
            path: Node::new(Path::from("test::Eq")),
            ty: parsed_trait_ty,
            fields: vec![],
            super_trait: Some(parsed_super_trait),
            directives: vec![],
        };
        let decl = Node::new(Decl::Trait(trait_decl));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let hash_def_id = DefId::new(FileId(0), 1);
        exports.insert("Hash".to_string(), DefTarget::Workspace(hash_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Hash should resolve to export
        assert_eq!(
            resolutions.get(&hash_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(hash_def_id))),
            "Super trait Hash should resolve to export"
        );

        // 'a in super trait should resolve to TypeParam
        let expected_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        assert_eq!(
            resolutions.get(&a_node_id),
            Some(&Resolution::TypeParam(expected_type_param_id)),
            "Type parameter 'a in super trait should resolve to TypeParam"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_trait_method_signature() {
        // trait Eq['a] { fn eq(self, other: 'a): bool }
        // 'a in method signature should resolve to trait's TypeParam
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create method parameter type: 'a
        let param_ty = Ty::var("'a");
        let param_node_id = NodeId::new();
        let mut parsed_param_ty = Parsed::new(TyScheme::from(param_ty), Source::default());
        parsed_param_ty.set_synthetic_ids(vec![param_node_id]);

        // Create method parameter: other: 'a
        let mut other_name = Name::new("other");
        other_name.ty = Some(parsed_param_ty);
        let other_param = Node::new(FnParam::Name(other_name));

        // Create method signature
        let method_sig = FuncSig {
            path: Node::new(Path::from("test::Eq::eq")),
            params: vec![other_param],
            ty_params: None,
            ret_ty: None,
            ty: None,
            modifiers: vec![],
            qualifiers: vec![],
            doc_comment: None,
            is_anon: false,
            is_method: true,
            has_body: false,
            span: Span::default(),
        };
        let method_decl = Node::new(Decl::FnSig(method_sig));

        // Create trait type: Eq['a]
        let trait_ty = Ty::proj("Eq", vec![Ty::var("'a")]);
        let parsed_trait_ty = Parsed::new(trait_ty, Source::default());

        // Create trait declaration
        let trait_decl = Trait {
            path: Node::new(Path::from("test::Eq")),
            ty: parsed_trait_ty,
            fields: vec![method_decl],
            super_trait: None,
            directives: vec![],
        };
        let decl = Node::new(Decl::Trait(trait_decl));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // 'a in method parameter should resolve to trait's TypeParam
        let expected_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        assert_eq!(
            resolutions.get(&param_node_id),
            Some(&Resolution::TypeParam(expected_type_param_id)),
            "Type parameter 'a in method signature should resolve to trait's TypeParam"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_trait_method_return_type() {
        // trait ToStr['a] { fn to_str(self): String }
        // String should resolve to export
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create method return type: String
        let ret_ty = Ty::con("String");
        let ret_node_id = NodeId::new();
        let mut parsed_ret_ty = Parsed::new(ret_ty, Source::default());
        parsed_ret_ty.set_synthetic_ids(vec![ret_node_id]);

        // Create method signature with return type
        let method_sig = FuncSig {
            path: Node::new(Path::from("test::ToStr::to_str")),
            params: vec![],
            ty_params: None,
            ret_ty: Some(parsed_ret_ty),
            ty: None,
            modifiers: vec![],
            qualifiers: vec![],
            doc_comment: None,
            is_anon: false,
            is_method: true,
            has_body: false,
            span: Span::default(),
        };
        let method_decl = Node::new(Decl::FnSig(method_sig));

        // Create trait type: ToStr['a]
        let trait_ty = Ty::proj("ToStr", vec![Ty::var("'a")]);
        let parsed_trait_ty = Parsed::new(trait_ty, Source::default());

        // Create trait declaration
        let trait_decl = Trait {
            path: Node::new(Path::from("test::ToStr")),
            ty: parsed_trait_ty,
            fields: vec![method_decl],
            super_trait: None,
            directives: vec![],
        };
        let decl = Node::new(Decl::Trait(trait_decl));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let string_def_id = DefId::new(FileId(0), 1);
        exports.insert("String".to_string(), DefTarget::Workspace(string_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // String should resolve to export
        assert_eq!(
            resolutions.get(&ret_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(string_def_id))),
            "Return type String should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_trait_no_type_params() {
        // trait Empty { fn foo(self): Bar }
        // Trait without type parameters should still resolve method types
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create method return type: Bar
        let ret_ty = Ty::con("Bar");
        let ret_node_id = NodeId::new();
        let mut parsed_ret_ty = Parsed::new(ret_ty, Source::default());
        parsed_ret_ty.set_synthetic_ids(vec![ret_node_id]);

        // Create method signature
        let method_sig = FuncSig {
            path: Node::new(Path::from("test::Empty::foo")),
            params: vec![],
            ty_params: None,
            ret_ty: Some(parsed_ret_ty),
            ty: None,
            modifiers: vec![],
            qualifiers: vec![],
            doc_comment: None,
            is_anon: false,
            is_method: true,
            has_body: false,
            span: Span::default(),
        };
        let method_decl = Node::new(Decl::FnSig(method_sig));

        // Create trait type: Empty (no type params - Ty::Const)
        let trait_ty = Ty::con("Empty");
        let parsed_trait_ty = Parsed::new(trait_ty, Source::default());

        // Create trait declaration
        let trait_decl = Trait {
            path: Node::new(Path::from("test::Empty")),
            ty: parsed_trait_ty,
            fields: vec![method_decl],
            super_trait: None,
            directives: vec![],
        };
        let decl = Node::new(Decl::Trait(trait_decl));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let bar_def_id = DefId::new(FileId(0), 1);
        exports.insert("Bar".to_string(), DefTarget::Workspace(bar_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Bar should resolve to export
        assert_eq!(
            resolutions.get(&ret_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(bar_def_id))),
            "Return type Bar should resolve to export"
        );
    }

    // =========================================================================
    // Tests for resolve_names_in_file with impl definitions
    // =========================================================================

    #[test]
    fn resolve_names_in_file_resolves_impl_trait_and_type() {
        // impl ToStr[Point]
        // ToStr and Point should resolve to exports
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create impl type: ToStr[Point]
        let impl_ty = Ty::proj("ToStr", vec![Ty::con("Point")]);
        let tostr_node_id = NodeId::new();
        let point_node_id = NodeId::new();
        let mut parsed_impl_ty = Parsed::new(impl_ty, Source::default());
        parsed_impl_ty.set_synthetic_ids(vec![tostr_node_id, point_node_id]);

        // Create impl declaration
        let impl_decl = Impl {
            ty: parsed_impl_ty,
            qualifiers: vec![],
            externs: None,
            funcs: None,
            consts: None,
            is_object: false,
        };
        let decl = Node::new(Decl::Impl(impl_decl));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let tostr_def_id = DefId::new(FileId(0), 1);
        let point_def_id = DefId::new(FileId(0), 2);
        exports.insert("ToStr".to_string(), DefTarget::Workspace(tostr_def_id));
        exports.insert("Point".to_string(), DefTarget::Workspace(point_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // ToStr should resolve to export
        assert_eq!(
            resolutions.get(&tostr_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(tostr_def_id))),
            "Trait ToStr should resolve to export"
        );

        // Point should resolve to export
        assert_eq!(
            resolutions.get(&point_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(point_def_id))),
            "Implementing type Point should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_impl_nested_type_args() {
        // impl Trait[Dict[String, Int]]
        // Trait, Dict, String, Int should all resolve
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create impl type: Trait[Dict[String, Int]]
        let inner_ty = Ty::proj("Dict", vec![Ty::con("String"), Ty::con("Int")]);
        let impl_ty = Ty::proj("Trait", vec![inner_ty]);
        let trait_node_id = NodeId::new();
        let dict_node_id = NodeId::new();
        let string_node_id = NodeId::new();
        let int_node_id = NodeId::new();
        let mut parsed_impl_ty = Parsed::new(impl_ty, Source::default());
        parsed_impl_ty.set_synthetic_ids(vec![
            trait_node_id,
            dict_node_id,
            string_node_id,
            int_node_id,
        ]);

        // Create impl declaration
        let impl_decl = Impl {
            ty: parsed_impl_ty,
            qualifiers: vec![],
            externs: None,
            funcs: None,
            consts: None,
            is_object: false,
        };
        let decl = Node::new(Decl::Impl(impl_decl));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let trait_def_id = DefId::new(FileId(0), 1);
        let dict_def_id = DefId::new(FileId(0), 2);
        let string_def_id = DefId::new(FileId(0), 3);
        let int_def_id = DefId::new(FileId(0), 4);
        exports.insert("Trait".to_string(), DefTarget::Workspace(trait_def_id));
        exports.insert("Dict".to_string(), DefTarget::Workspace(dict_def_id));
        exports.insert("String".to_string(), DefTarget::Workspace(string_def_id));
        exports.insert("Int".to_string(), DefTarget::Workspace(int_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // All types should resolve
        assert_eq!(
            resolutions.get(&trait_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(trait_def_id))),
            "Trait should resolve to export"
        );
        assert_eq!(
            resolutions.get(&dict_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(dict_def_id))),
            "Dict should resolve to export"
        );
        assert_eq!(
            resolutions.get(&string_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(string_def_id))),
            "String should resolve to export"
        );
        assert_eq!(
            resolutions.get(&int_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(int_def_id))),
            "Int should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_impl_method_signature() {
        // impl ToStr[Point] { fn to_str(self): String }
        // String in method return type should resolve
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create method return type: String
        let ret_ty = Ty::con("String");
        let ret_node_id = NodeId::new();
        let mut parsed_ret_ty = Parsed::new(ret_ty, Source::default());
        parsed_ret_ty.set_synthetic_ids(vec![ret_node_id]);

        // Create method signature
        let method_sig = FuncSig {
            path: Node::new(Path::from("test::ToStr::to_str")),
            params: vec![],
            ty_params: None,
            ret_ty: Some(parsed_ret_ty),
            ty: None,
            modifiers: vec![],
            qualifiers: vec![],
            doc_comment: None,
            is_anon: false,
            is_method: true,
            has_body: true,
            span: Span::default(),
        };
        let method = Func {
            sig: method_sig,
            body: None,
        };
        let method_decl = Node::new(Decl::Func(method));

        // Create impl type: ToStr[Point]
        // Need synthetic IDs for the impl type even though we don't check them
        let impl_ty = Ty::proj("ToStr", vec![Ty::con("Point")]);
        let mut parsed_impl_ty = Parsed::new(impl_ty, Source::default());
        parsed_impl_ty.set_synthetic_ids(vec![NodeId::new(), NodeId::new()]); // ToStr, Point

        // Create impl declaration
        let impl_decl = Impl {
            ty: parsed_impl_ty,
            qualifiers: vec![],
            externs: None,
            funcs: Some(vec![method_decl]),
            consts: None,
            is_object: false,
        };
        let decl = Node::new(Decl::Impl(impl_decl));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let string_def_id = DefId::new(FileId(0), 1);
        exports.insert("String".to_string(), DefTarget::Workspace(string_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // String should resolve to export
        assert_eq!(
            resolutions.get(&ret_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(string_def_id))),
            "Method return type String should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_object_impl() {
        // impl object Point { fn foo(self): Bar }
        // Point and Bar should resolve
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create method return type: Bar
        let ret_ty = Ty::con("Bar");
        let ret_node_id = NodeId::new();
        let mut parsed_ret_ty = Parsed::new(ret_ty, Source::default());
        parsed_ret_ty.set_synthetic_ids(vec![ret_node_id]);

        // Create method signature
        let method_sig = FuncSig {
            path: Node::new(Path::from("test::Point::foo")),
            params: vec![],
            ty_params: None,
            ret_ty: Some(parsed_ret_ty),
            ty: None,
            modifiers: vec![],
            qualifiers: vec![],
            doc_comment: None,
            is_anon: false,
            is_method: true,
            has_body: true,
            span: Span::default(),
        };
        let method = Func {
            sig: method_sig,
            body: None,
        };
        let method_decl = Node::new(Decl::Func(method));

        // Create impl type: Point (object impl)
        let impl_ty = Ty::con("Point");
        let point_node_id = NodeId::new();
        let mut parsed_impl_ty = Parsed::new(impl_ty, Source::default());
        parsed_impl_ty.set_synthetic_ids(vec![point_node_id]);

        // Create impl declaration (object impl)
        let impl_decl = Impl {
            ty: parsed_impl_ty,
            qualifiers: vec![],
            externs: None,
            funcs: Some(vec![method_decl]),
            consts: None,
            is_object: true,
        };
        let decl = Node::new(Decl::Impl(impl_decl));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let point_def_id = DefId::new(FileId(0), 1);
        let bar_def_id = DefId::new(FileId(0), 2);
        exports.insert("Point".to_string(), DefTarget::Workspace(point_def_id));
        exports.insert("Bar".to_string(), DefTarget::Workspace(bar_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Point should resolve to export
        assert_eq!(
            resolutions.get(&point_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(point_def_id))),
            "Implementing type Point should resolve to export"
        );

        // Bar should resolve to export
        assert_eq!(
            resolutions.get(&ret_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(bar_def_id))),
            "Method return type Bar should resolve to export"
        );
    }

    // =========================================================================
    // Tests for resolve_names_in_file with function definitions
    // =========================================================================

    #[test]
    fn resolve_names_in_file_resolves_func_param_type() {
        // fn foo(x: Point) {}
        // Point in parameter type should resolve to export
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create parameter type: Point
        let param_ty = Ty::con("Point");
        let param_type_node_id = NodeId::new();
        let mut parsed_param_ty = Parsed::new(TyScheme::from(param_ty), Source::default());
        parsed_param_ty.set_synthetic_ids(vec![param_type_node_id]);

        // Create parameter: x: Point
        let mut x_name = Name::new("x");
        x_name.ty = Some(parsed_param_ty);
        let x_param = Node::new(FnParam::Name(x_name));

        // Create function
        let func_body = Node::new(Expr::Block(Block { stmts: vec![] }));
        let func = Func::new(Node::new(Path::from("test::foo")), vec![x_param], func_body);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let point_def_id = DefId::new(FileId(0), 1);
        exports.insert("Point".to_string(), DefTarget::Workspace(point_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Point should resolve to export
        assert_eq!(
            resolutions.get(&param_type_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(point_def_id))),
            "Parameter type Point should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_func_return_type() {
        // fn foo(): String {}
        // String in return type should resolve to export
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create return type: String
        let ret_ty = Ty::con("String");
        let ret_node_id = NodeId::new();
        let mut parsed_ret_ty = Parsed::new(ret_ty, Source::default());
        parsed_ret_ty.set_synthetic_ids(vec![ret_node_id]);

        // Create function with return type
        let func_body = Node::new(Expr::Block(Block { stmts: vec![] }));
        let mut func = Func::new(Node::new(Path::from("test::foo")), vec![], func_body);
        func.sig.ret_ty = Some(parsed_ret_ty);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let string_def_id = DefId::new(FileId(0), 1);
        exports.insert("String".to_string(), DefTarget::Workspace(string_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // String should resolve to export
        assert_eq!(
            resolutions.get(&ret_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(string_def_id))),
            "Return type String should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_func_type_param() {
        // fn foo['a](x: 'a): 'a {}
        // 'a should resolve to TypeParam in both parameter and return type
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create parameter type: 'a
        let param_ty = Ty::var("'a");
        let param_type_node_id = NodeId::new();
        let mut parsed_param_ty = Parsed::new(TyScheme::from(param_ty), Source::default());
        parsed_param_ty.set_synthetic_ids(vec![param_type_node_id]);

        // Create return type: 'a
        let ret_ty = Ty::var("'a");
        let ret_node_id = NodeId::new();
        let mut parsed_ret_ty = Parsed::new(ret_ty, Source::default());
        parsed_ret_ty.set_synthetic_ids(vec![ret_node_id]);

        // Create type parameter
        let ty_param = Ty::var("'a");
        let ty_param_parsed = Parsed::new(ty_param, Source::default());

        // Create parameter: x: 'a
        let mut x_name = Name::new("x");
        x_name.ty = Some(parsed_param_ty);
        let x_param = Node::new(FnParam::Name(x_name));

        // Create function with type parameter
        let func_body = Node::new(Expr::Block(Block { stmts: vec![] }));
        let mut func = Func::new(Node::new(Path::from("test::foo")), vec![x_param], func_body);
        func.sig.ty_params = Some(TypeParams {
            tys: vec![ty_param_parsed],
            lb_span: Span::default(),
            rb_span: Span::default(),
        });
        func.sig.ret_ty = Some(parsed_ret_ty);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // 'a in parameter type should resolve to TypeParam
        let expected_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        assert_eq!(
            resolutions.get(&param_type_node_id),
            Some(&Resolution::TypeParam(expected_type_param_id)),
            "Parameter type 'a should resolve to TypeParam"
        );

        // 'a in return type should resolve to TypeParam
        assert_eq!(
            resolutions.get(&ret_node_id),
            Some(&Resolution::TypeParam(expected_type_param_id)),
            "Return type 'a should resolve to TypeParam"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_func_qualifier() {
        // fn foo['a](x: 'a) where ToStr['a] {}
        // ToStr and 'a in qualifier should resolve
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create qualifier type: ToStr['a]
        let qualifier_ty = Ty::proj("ToStr", vec![Ty::var("'a")]);
        let tostr_node_id = NodeId::new();
        let a_node_id = NodeId::new();
        let mut parsed_qualifier = Parsed::new(qualifier_ty, Source::default());
        parsed_qualifier.set_synthetic_ids(vec![tostr_node_id, a_node_id]);

        // Create type parameter
        let ty_param = Ty::var("'a");
        let ty_param_parsed = Parsed::new(ty_param, Source::default());

        // Create function with qualifier
        let func_body = Node::new(Expr::Block(Block { stmts: vec![] }));
        let mut func = Func::new(Node::new(Path::from("test::foo")), vec![], func_body);
        func.sig.ty_params = Some(TypeParams {
            tys: vec![ty_param_parsed],
            lb_span: Span::default(),
            rb_span: Span::default(),
        });
        func.sig.qualifiers = vec![parsed_qualifier];
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let tostr_def_id = DefId::new(FileId(0), 1);
        exports.insert("ToStr".to_string(), DefTarget::Workspace(tostr_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // ToStr should resolve to export
        assert_eq!(
            resolutions.get(&tostr_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(tostr_def_id))),
            "Qualifier trait ToStr should resolve to export"
        );

        // 'a in qualifier should resolve to TypeParam
        let expected_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        assert_eq!(
            resolutions.get(&a_node_id),
            Some(&Resolution::TypeParam(expected_type_param_id)),
            "Type parameter 'a in qualifier should resolve to TypeParam"
        );
    }

    // =========================================================================
    // Tests for resolve_names_in_file with type alias definitions
    // =========================================================================

    #[test]
    fn resolve_names_in_file_resolves_type_alias_simple() {
        // typealias MyInt = Int
        // Int should resolve to export
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create aliased type: Int
        let aliased_ty = Ty::con("Int");
        let int_node_id = NodeId::new();
        let mut parsed_aliased_ty = Parsed::new(aliased_ty, Source::default());
        parsed_aliased_ty.set_synthetic_ids(vec![int_node_id]);

        // Create type alias name
        let name = Node::new(Name::new("MyInt"));

        // Create type alias declaration
        let decl = Node::new(Decl::TypeAlias(name, parsed_aliased_ty));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let int_def_id = DefId::new(FileId(0), 1);
        exports.insert("Int".to_string(), DefTarget::Workspace(int_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Int should resolve to export
        assert_eq!(
            resolutions.get(&int_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(int_def_id))),
            "Aliased type Int should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_type_alias_generic() {
        // typealias IntList = List[Int]
        // List and Int should both resolve to exports
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create aliased type: List[Int]
        let aliased_ty = Ty::proj("List", vec![Ty::con("Int")]);
        let list_node_id = NodeId::new();
        let int_node_id = NodeId::new();
        let mut parsed_aliased_ty = Parsed::new(aliased_ty, Source::default());
        parsed_aliased_ty.set_synthetic_ids(vec![list_node_id, int_node_id]);

        // Create type alias name
        let name = Node::new(Name::new("IntList"));

        // Create type alias declaration
        let decl = Node::new(Decl::TypeAlias(name, parsed_aliased_ty));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let list_def_id = DefId::new(FileId(0), 1);
        let int_def_id = DefId::new(FileId(0), 2);
        exports.insert("List".to_string(), DefTarget::Workspace(list_def_id));
        exports.insert("Int".to_string(), DefTarget::Workspace(int_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // List should resolve to export
        assert_eq!(
            resolutions.get(&list_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(list_def_id))),
            "List should resolve to export"
        );

        // Int should resolve to export
        assert_eq!(
            resolutions.get(&int_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(int_def_id))),
            "Int should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_type_alias_nested() {
        // typealias StringIntDict = Dict[String, Int]
        // Dict, String, and Int should all resolve to exports
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create aliased type: Dict[String, Int]
        let aliased_ty = Ty::proj("Dict", vec![Ty::con("String"), Ty::con("Int")]);
        let dict_node_id = NodeId::new();
        let string_node_id = NodeId::new();
        let int_node_id = NodeId::new();
        let mut parsed_aliased_ty = Parsed::new(aliased_ty, Source::default());
        parsed_aliased_ty.set_synthetic_ids(vec![dict_node_id, string_node_id, int_node_id]);

        // Create type alias name
        let name = Node::new(Name::new("StringIntDict"));

        // Create type alias declaration
        let decl = Node::new(Decl::TypeAlias(name, parsed_aliased_ty));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let dict_def_id = DefId::new(FileId(0), 1);
        let string_def_id = DefId::new(FileId(0), 2);
        let int_def_id = DefId::new(FileId(0), 3);
        exports.insert("Dict".to_string(), DefTarget::Workspace(dict_def_id));
        exports.insert("String".to_string(), DefTarget::Workspace(string_def_id));
        exports.insert("Int".to_string(), DefTarget::Workspace(int_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Dict should resolve to export
        assert_eq!(
            resolutions.get(&dict_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(dict_def_id))),
            "Dict should resolve to export"
        );

        // String should resolve to export
        assert_eq!(
            resolutions.get(&string_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(string_def_id))),
            "String should resolve to export"
        );

        // Int should resolve to export
        assert_eq!(
            resolutions.get(&int_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(int_def_id))),
            "Int should resolve to export"
        );
    }

    // =========================================================================
    // Tests for resolve_names_in_file with annotated bindings
    // =========================================================================

    #[test]
    fn resolve_names_in_file_resolves_annotated_name_binding() {
        // x: Point (immutable binding with type annotation)
        // Point should resolve to export
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create type annotation: Point
        let ty = Ty::con("Point");
        let point_node_id = NodeId::new();
        let mut parsed_ty = Parsed::new(TyScheme::from(ty), Source::default());
        parsed_ty.set_synthetic_ids(vec![point_node_id]);

        // Create name binding with type annotation
        let name = Name::typed("x", parsed_ty);
        let name_decl = Node::new(Decl::Name(Node::new(name)));

        let file = test_file(vec![name_decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let point_def_id = DefId::new(FileId(0), 1);
        exports.insert("Point".to_string(), DefTarget::Workspace(point_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Point should resolve to export
        assert_eq!(
            resolutions.get(&point_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(point_def_id))),
            "Type annotation Point should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_annotated_mutable_binding() {
        // mut x: String (mutable binding with type annotation)
        // String should resolve to export
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create type annotation: String
        let ty = Ty::con("String");
        let string_node_id = NodeId::new();
        let mut parsed_ty = Parsed::new(TyScheme::from(ty), Source::default());
        parsed_ty.set_synthetic_ids(vec![string_node_id]);

        // Create mutable binding with type annotation
        let name = Name::typed("x", parsed_ty);
        let mutable_decl = Node::new(Decl::Mutable(Node::new(name)));

        let file = test_file(vec![mutable_decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let string_def_id = DefId::new(FileId(0), 1);
        exports.insert("String".to_string(), DefTarget::Workspace(string_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // String should resolve to export
        assert_eq!(
            resolutions.get(&string_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(string_def_id))),
            "Type annotation String should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_annotated_declare() {
        // x: Int = 5 (declaration with type annotation)
        // Int should resolve to export
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create type annotation: Int
        let ty = Ty::con("Int");
        let int_node_id = NodeId::new();
        let mut parsed_ty = Parsed::new(TyScheme::from(ty), Source::default());
        parsed_ty.set_synthetic_ids(vec![int_node_id]);

        // Create name with type annotation
        let name = Name::typed("x", parsed_ty);

        // Create assignment: x: Int = true (using bool for simplicity)
        let lhs = Node::new(AstPattern::Name(name));
        let rhs = Node::new(Expr::Literal(Literal::Bool(true)));
        let assign = Assign {
            lhs,
            rhs: Box::new(rhs),
            is_mut: false,
            mut_span: None,
            op: crate::ast::InfixOp::Assign,
            op_span: Span::new(),
        };
        let declare_decl = Node::new(Decl::Declare(assign));

        let file = test_file(vec![declare_decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let int_def_id = DefId::new(FileId(0), 1);
        exports.insert("Int".to_string(), DefTarget::Workspace(int_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Int should resolve to export
        assert_eq!(
            resolutions.get(&int_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(int_def_id))),
            "Type annotation Int should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_annotated_binding_generic() {
        // x: List[Int] (binding with generic type annotation)
        // List and Int should both resolve to exports
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create type annotation: List[Int]
        let ty = Ty::proj("List", vec![Ty::con("Int")]);
        let list_node_id = NodeId::new();
        let int_node_id = NodeId::new();
        let mut parsed_ty = Parsed::new(TyScheme::from(ty), Source::default());
        parsed_ty.set_synthetic_ids(vec![list_node_id, int_node_id]);

        // Create name binding with type annotation
        let name = Name::typed("x", parsed_ty);
        let name_decl = Node::new(Decl::Name(Node::new(name)));

        let file = test_file(vec![name_decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let list_def_id = DefId::new(FileId(0), 1);
        let int_def_id = DefId::new(FileId(0), 2);
        exports.insert("List".to_string(), DefTarget::Workspace(list_def_id));
        exports.insert("Int".to_string(), DefTarget::Workspace(int_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // List should resolve to export
        assert_eq!(
            resolutions.get(&list_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(list_def_id))),
            "List should resolve to export"
        );

        // Int should resolve to export
        assert_eq!(
            resolutions.get(&int_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(int_def_id))),
            "Int should resolve to export"
        );
    }

    // =========================================================================
    // Tests for resolve_names_in_file with extern declarations
    // =========================================================================

    #[test]
    fn resolve_names_in_file_resolves_extern_fn_param_type() {
        // extern fn read(fd: int, buf: String): int
        // String should resolve to export
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create parameter type: String
        let param_ty = Ty::con("String");
        let param_node_id = NodeId::new();
        let mut parsed_param_ty = Parsed::new(TyScheme::from(param_ty), Source::default());
        parsed_param_ty.set_synthetic_ids(vec![param_node_id]);

        // Create parameter: buf: String
        let mut buf_name = Name::new("buf");
        buf_name.ty = Some(parsed_param_ty);
        let buf_param = Node::new(FnParam::Name(buf_name));

        // Create extern function signature
        let sig = FuncSig {
            path: Node::new(Path::from("read")),
            params: vec![buf_param],
            ty_params: None,
            ret_ty: None,
            ty: None,
            modifiers: vec![],
            qualifiers: vec![],
            doc_comment: None,
            is_anon: false,
            is_method: false,
            has_body: false,
            span: Span::default(),
        };
        let fnsig_decl = Node::new(Decl::FnSig(sig));
        let extern_decl = Node::new(Decl::Extern(Extern::new(fnsig_decl)));

        let file = test_file(vec![extern_decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let string_def_id = DefId::new(FileId(0), 1);
        exports.insert("String".to_string(), DefTarget::Workspace(string_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // String should resolve to export
        assert_eq!(
            resolutions.get(&param_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(string_def_id))),
            "Extern fn parameter type String should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_extern_fn_return_type() {
        // extern fn malloc(size: int): RawPtr[u8]
        // RawPtr and u8 should resolve to exports
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create return type: RawPtr[u8]
        let ret_ty = Ty::proj("RawPtr", vec![Ty::con("u8")]);
        let rawptr_node_id = NodeId::new();
        let u8_node_id = NodeId::new();
        let mut parsed_ret_ty = Parsed::new(ret_ty, Source::default());
        parsed_ret_ty.set_synthetic_ids(vec![rawptr_node_id, u8_node_id]);

        // Create extern function signature
        let sig = FuncSig {
            path: Node::new(Path::from("malloc")),
            params: vec![],
            ty_params: None,
            ret_ty: Some(parsed_ret_ty),
            ty: None,
            modifiers: vec![],
            qualifiers: vec![],
            doc_comment: None,
            is_anon: false,
            is_method: false,
            has_body: false,
            span: Span::default(),
        };
        let fnsig_decl = Node::new(Decl::FnSig(sig));
        let extern_decl = Node::new(Decl::Extern(Extern::new(fnsig_decl)));

        let file = test_file(vec![extern_decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let rawptr_def_id = DefId::new(FileId(0), 1);
        let u8_def_id = DefId::new(FileId(0), 2);
        exports.insert("RawPtr".to_string(), DefTarget::Workspace(rawptr_def_id));
        exports.insert("u8".to_string(), DefTarget::Workspace(u8_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // RawPtr should resolve to export
        assert_eq!(
            resolutions.get(&rawptr_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(rawptr_def_id))),
            "Extern fn return type RawPtr should resolve to export"
        );

        // u8 should resolve to export
        assert_eq!(
            resolutions.get(&u8_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(u8_def_id))),
            "Extern fn return type u8 should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_extern_fn_generic() {
        // extern fn qsort['a](arr: RawPtr['a], cmp: Fn['a, 'a, int]): ()
        // Type params should resolve correctly
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create type parameter 'a for the type_params
        let ty_param_a = Ty::var("'a");
        let mut parsed_ty_param = Parsed::new(ty_param_a, Source::default());
        parsed_ty_param.set_synthetic_ids(vec![NodeId::new()]);

        // Create parameter type: RawPtr['a]
        let param_ty = Ty::proj("RawPtr", vec![Ty::var("'a")]);
        let rawptr_node_id = NodeId::new();
        let a_node_id = NodeId::new();
        let mut parsed_param_ty = Parsed::new(TyScheme::from(param_ty), Source::default());
        parsed_param_ty.set_synthetic_ids(vec![rawptr_node_id, a_node_id]);

        // Create parameter: arr: RawPtr['a]
        let mut arr_name = Name::new("arr");
        arr_name.ty = Some(parsed_param_ty);
        let arr_param = Node::new(FnParam::Name(arr_name));

        // Create extern function signature with type params
        let sig = FuncSig {
            path: Node::new(Path::from("qsort")),
            params: vec![arr_param],
            ty_params: Some(TypeParams {
                tys: vec![parsed_ty_param],
                lb_span: Span::default(),
                rb_span: Span::default(),
            }),
            ret_ty: None,
            ty: None,
            modifiers: vec![],
            qualifiers: vec![],
            doc_comment: None,
            is_anon: false,
            is_method: false,
            has_body: false,
            span: Span::default(),
        };
        let fnsig_decl = Node::new(Decl::FnSig(sig));
        let extern_decl = Node::new(Decl::Extern(Extern::new(fnsig_decl)));

        let file = test_file(vec![extern_decl], vec![]);
        let imports = HashMap::new();
        let mut exports = HashMap::new();
        let rawptr_def_id = DefId::new(FileId(0), 1);
        exports.insert("RawPtr".to_string(), DefTarget::Workspace(rawptr_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // RawPtr should resolve to export
        assert_eq!(
            resolutions.get(&rawptr_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(rawptr_def_id))),
            "Extern fn parameter type RawPtr should resolve to export"
        );

        // 'a should resolve to TypeParam
        let expected_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        assert_eq!(
            resolutions.get(&a_node_id),
            Some(&Resolution::TypeParam(expected_type_param_id)),
            "Type parameter 'a in extern fn should resolve to TypeParam"
        );
    }

    #[test]
    fn resolve_names_in_file_extern_fn_not_double_resolved() {
        // Verify that extern fn signatures are not resolved twice (once by Extern handler,
        // once by walker visiting the inner FnSig)
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create type parameter 'a
        let ty_param_a = Ty::var("'a");
        let mut parsed_ty_param = Parsed::new(ty_param_a, Source::default());
        parsed_ty_param.set_synthetic_ids(vec![NodeId::new()]);

        // Create parameter type that uses 'a
        let param_ty = Ty::var("'a");
        let a_node_id = NodeId::new();
        let mut parsed_param_ty = Parsed::new(TyScheme::from(param_ty), Source::default());
        parsed_param_ty.set_synthetic_ids(vec![a_node_id]);

        // Create parameter: x: 'a
        let mut x_name = Name::new("x");
        x_name.ty = Some(parsed_param_ty);
        let x_param = Node::new(FnParam::Name(x_name));

        // Create extern function signature with type params
        let sig = FuncSig {
            path: Node::new(Path::from("identity")),
            params: vec![x_param],
            ty_params: Some(TypeParams {
                tys: vec![parsed_ty_param],
                lb_span: Span::default(),
                rb_span: Span::default(),
            }),
            ret_ty: None,
            ty: None,
            modifiers: vec![],
            qualifiers: vec![],
            doc_comment: None,
            is_anon: false,
            is_method: false,
            has_body: false,
            span: Span::default(),
        };
        let fnsig_decl = Node::new(Decl::FnSig(sig));
        let extern_decl = Node::new(Decl::Extern(Extern::new(fnsig_decl)));

        let file = test_file(vec![extern_decl], vec![]);
        let imports = HashMap::new();
        let exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // 'a should resolve to TypeParam, not Error
        // If it resolves to Error, that means the walker re-processed the FnSig
        // without the type params from the extern fn's signature
        let expected_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        assert_eq!(
            resolutions.get(&a_node_id),
            Some(&Resolution::TypeParam(expected_type_param_id)),
            "Type parameter 'a should resolve to TypeParam (not Error from double-resolution)"
        );
    }

    // =========================================================================
    // Tests for expression type resolution (Cast, New, Type)
    // =========================================================================

    #[test]
    fn resolve_names_in_file_resolves_cast_type() {
        // fn f() { 42 as Point }  where Point is a struct export
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create the type in the cast: Point
        let ty = Ty::con("Point");
        let type_node_id = NodeId::new();
        let mut parsed_ty = Parsed::new(ty, Source::default());
        parsed_ty.set_synthetic_ids(vec![type_node_id]);

        // Create cast expression: x as Point
        let lhs = Box::new(Node::new(Expr::Name(Name::new("x"))));
        let cast_expr = Node::new(Expr::Cast(Cast {
            lhs,
            ty: parsed_ty,
            as_span: Span::default(),
        }));

        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![cast_expr],
        }));
        let func = Func::new(Node::new(Path::from("test::f")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();

        // Point is exported from the module
        let point_def_id = DefId::new(FileId(0), 1);
        let mut exports = HashMap::new();
        exports.insert("Point".to_string(), DefTarget::Workspace(point_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Cast type should resolve to Point struct
        assert!(
            resolutions.contains_key(&type_node_id),
            "Cast type should have resolution"
        );
        assert_eq!(
            resolutions.get(&type_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(point_def_id))),
            "Cast type should resolve to Point struct"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_cast_type_with_type_param() {
        // fn f['a]() { 42 as 'a }  where 'a is a type parameter
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create type parameter 'a for the function
        let ty_param_a = Ty::var("'a");
        let mut parsed_ty_param = Parsed::new(ty_param_a, Source::default());
        parsed_ty_param.set_synthetic_ids(vec![NodeId::new()]);

        // Create the type in the cast: 'a
        let ty = Ty::var("'a");
        let type_node_id = NodeId::new();
        let mut parsed_ty = Parsed::new(ty, Source::default());
        parsed_ty.set_synthetic_ids(vec![type_node_id]);

        // Create cast expression: x as 'a
        let lhs = Box::new(Node::new(Expr::Name(Name::new("x"))));
        let cast_expr = Node::new(Expr::Cast(Cast {
            lhs,
            ty: parsed_ty,
            as_span: Span::default(),
        }));

        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![cast_expr],
        }));
        let mut func = Func::new(Node::new(Path::from("test::f")), vec![], func_body);
        func.sig.ty_params = Some(TypeParams {
            tys: vec![parsed_ty_param],
            lb_span: Span::default(),
            rb_span: Span::default(),
        });
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Cast type should resolve to type parameter
        let expected_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        assert!(
            resolutions.contains_key(&type_node_id),
            "Cast type should have resolution"
        );
        assert_eq!(
            resolutions.get(&type_node_id),
            Some(&Resolution::TypeParam(expected_type_param_id)),
            "Cast type 'a should resolve to TypeParam"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_new_type() {
        // fn f() { new(Point, 10) }  where Point is a struct export
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create the type in new: Point
        let ty = Ty::con("Point");
        let type_node_id = NodeId::new();
        let mut parsed_ty = Parsed::new(ty, Source::default());
        parsed_ty.set_synthetic_ids(vec![type_node_id]);

        // Create new expression: new(Point, n)
        let count = Some(Box::new(Node::new(Expr::Name(Name::new("n")))));
        let new_expr = Node::new(Expr::New(New {
            ty: Node::new(parsed_ty),
            count,
            new_span: Span::default(),
            paren_span: Span::default(),
        }));

        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![new_expr],
        }));
        let func = Func::new(Node::new(Path::from("test::f")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();

        // Point is exported from the module
        let point_def_id = DefId::new(FileId(0), 1);
        let mut exports = HashMap::new();
        exports.insert("Point".to_string(), DefTarget::Workspace(point_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // New type should resolve to Point struct
        assert!(
            resolutions.contains_key(&type_node_id),
            "New type should have resolution"
        );
        assert_eq!(
            resolutions.get(&type_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(point_def_id))),
            "New type should resolve to Point struct"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_type_expression() {
        // fn f() { sizeof(Point) }  where Point is a struct export (Type expression)
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create the type expression: Point (as TyScheme)
        let ty = Ty::con("Point");
        let type_node_id = NodeId::new();
        let mut parsed_ty_scheme = Parsed::new(TyScheme::from(ty), Source::default());
        parsed_ty_scheme.set_synthetic_ids(vec![type_node_id]);

        // Create type expression: sizeof(Point) represented as Expr::Type
        let type_expr = Node::new(Expr::Type(parsed_ty_scheme));

        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![type_expr],
        }));
        let func = Func::new(Node::new(Path::from("test::f")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();

        // Point is exported from the module
        let point_def_id = DefId::new(FileId(0), 1);
        let mut exports = HashMap::new();
        exports.insert("Point".to_string(), DefTarget::Workspace(point_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Type expression should resolve to Point struct
        assert!(
            resolutions.contains_key(&type_node_id),
            "Type expression should have resolution"
        );
        assert_eq!(
            resolutions.get(&type_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(point_def_id))),
            "Type expression should resolve to Point struct"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_cast_in_impl_method_with_impl_type_param() {
        // impl object Container['a] { fn cast_it(self) { x as 'a } }
        // Verifies that impl-level type params are in scope for method bodies
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create the cast type: 'a (referencing impl's type param)
        let cast_ty = Ty::var("'a");
        let cast_type_node_id = NodeId::new();
        let mut cast_parsed_ty = Parsed::new(cast_ty, Source::default());
        cast_parsed_ty.set_synthetic_ids(vec![cast_type_node_id]);

        // Create cast expression: x as 'a
        let lhs = Box::new(Node::new(Expr::Name(Name::new("x"))));
        let cast_expr = Node::new(Expr::Cast(Cast {
            lhs,
            ty: cast_parsed_ty,
            as_span: Span::default(),
        }));

        // Create method with body containing cast
        let method_body = Node::new(Expr::Block(Block {
            stmts: vec![cast_expr],
        }));
        let method = Func::new(Node::new(Path::from("cast_it")), vec![], method_body);
        let method_decl = Node::new(Decl::Func(method));

        // Create impl type: Container['a]
        let impl_ty = Ty::proj("Container", vec![Ty::var("'a")]);
        let container_node_id = NodeId::new();
        let a_impl_node_id = NodeId::new();
        let mut impl_parsed_ty = Parsed::new(impl_ty, Source::default());
        impl_parsed_ty.set_synthetic_ids(vec![container_node_id, a_impl_node_id]);

        // Create the impl block
        let imp = Impl {
            ty: impl_parsed_ty,
            qualifiers: vec![],
            externs: None,
            funcs: Some(vec![method_decl]),
            consts: None,
            is_object: true,
        };
        let impl_decl = Node::new(Decl::Impl(imp));

        let file = test_file(vec![impl_decl], vec![]);
        let imports = HashMap::new();

        // Container is exported
        let container_def_id = DefId::new(FileId(0), 1);
        let mut exports = HashMap::new();
        exports.insert(
            "Container".to_string(),
            DefTarget::Workspace(container_def_id),
        );

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Cast type 'a in method body should resolve to impl's type parameter
        // The owner is the impl's def_id (from impl_decl.id.owner)
        let expected_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        assert!(
            resolutions.contains_key(&cast_type_node_id),
            "Cast type in impl method should have resolution"
        );
        assert_eq!(
            resolutions.get(&cast_type_node_id),
            Some(&Resolution::TypeParam(expected_type_param_id)),
            "Cast type 'a should resolve to impl's TypeParam"
        );
    }

    // =========================================================================
    // Tests for ScopedAccess type resolution
    // =========================================================================

    #[test]
    fn resolve_names_in_file_resolves_scoped_access_lhs_type() {
        // fn f() { Math[int]::double }
        // The LHS type Math[int] should be resolved: Math -> export, int -> builtin
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create the LHS type: Math[int]
        let lhs_ty = Ty::proj("Math", vec![Ty::con("int")]);
        let math_node_id = NodeId::new();
        let int_node_id = NodeId::new();
        let mut parsed_lhs_ty = Parsed::new(TyScheme::from(lhs_ty), Source::default());
        parsed_lhs_ty.set_synthetic_ids(vec![math_node_id, int_node_id]);

        // Create the LHS expression: Expr::Type(Math[int])
        let lhs_expr = Node::new(Expr::Type(parsed_lhs_ty));

        // Create the RHS name: double
        let rhs_name = Node::new(Name::new("double"));

        // Create ScopedAccess: Math[int]::double
        let scoped_access = ScopedAccess {
            lhs: Box::new(lhs_expr),
            rhs: rhs_name,
            sep: Token {
                kind: TokenKind::DoubleColon,
                span: Span::default(),
            },
        };
        let scoped_access_expr = Node::new(Expr::ScopedAccess(scoped_access));

        // Create function containing the scoped access
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![scoped_access_expr],
        }));
        let func = Func::new(Node::new(Path::from("test::f")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();

        // Math is exported, int is also exported (simulating builtin)
        let math_def_id = DefId::new(FileId(0), 1);
        let int_def_id = DefId::new(FileId(0), 2);
        let mut exports = HashMap::new();
        exports.insert("Math".to_string(), DefTarget::Workspace(math_def_id));
        exports.insert("int".to_string(), DefTarget::Workspace(int_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Math should be resolved
        assert!(
            resolutions.contains_key(&math_node_id),
            "Math in ScopedAccess LHS should have resolution"
        );
        assert_eq!(
            resolutions.get(&math_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(math_def_id))),
            "Math should resolve to export"
        );

        // int should be resolved
        assert!(
            resolutions.contains_key(&int_node_id),
            "int in ScopedAccess LHS should have resolution"
        );
        assert_eq!(
            resolutions.get(&int_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(int_def_id))),
            "int should resolve to export"
        );
    }

    #[test]
    fn resolve_names_in_file_resolves_scoped_access_lhs_with_type_param() {
        // impl Container['a] { fn f() { Container['a]::helper } }
        // The LHS type Container['a] should be resolved: Container -> export, 'a -> TypeParam
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        // Create the LHS type: Container['a]
        let lhs_ty = Ty::proj("Container", vec![Ty::var("'a")]);
        let container_node_id = NodeId::new();
        let a_node_id = NodeId::new();
        let mut parsed_lhs_ty = Parsed::new(TyScheme::from(lhs_ty), Source::default());
        parsed_lhs_ty.set_synthetic_ids(vec![container_node_id, a_node_id]);

        // Create the LHS expression: Expr::Type(Container['a])
        let lhs_expr = Node::new(Expr::Type(parsed_lhs_ty));

        // Create the RHS name: helper
        let rhs_name = Node::new(Name::new("helper"));

        // Create ScopedAccess: Container['a]::helper
        let scoped_access = ScopedAccess {
            lhs: Box::new(lhs_expr),
            rhs: rhs_name,
            sep: Token {
                kind: TokenKind::DoubleColon,
                span: Span::default(),
            },
        };
        let scoped_access_expr = Node::new(Expr::ScopedAccess(scoped_access));

        // Create method containing the scoped access
        let method_body = Node::new(Expr::Block(Block {
            stmts: vec![scoped_access_expr],
        }));
        let method = Func::new(
            Node::new(Path::from("test::Container::f")),
            vec![],
            method_body,
        );
        let method_decl = Node::new(Decl::Func(method));

        // Create impl type: Container['a]
        let impl_ty = Ty::proj("Container", vec![Ty::var("'a")]);
        let mut impl_parsed_ty = Parsed::new(impl_ty, Source::default());
        // Need synthetic IDs for the impl type (Container and 'a)
        impl_parsed_ty.set_synthetic_ids(vec![NodeId::new(), NodeId::new()]);

        // Create impl declaration
        let imp = Impl {
            ty: impl_parsed_ty,
            qualifiers: vec![],
            externs: None,
            funcs: Some(vec![method_decl]),
            consts: None,
            is_object: true,
        };
        let impl_decl = Node::new(Decl::Impl(imp));

        let file = test_file(vec![impl_decl], vec![]);
        let imports = HashMap::new();

        // Container is exported
        let container_def_id = DefId::new(FileId(0), 1);
        let mut exports = HashMap::new();
        exports.insert(
            "Container".to_string(),
            DefTarget::Workspace(container_def_id),
        );

        let resolutions = resolve_names_in_file(&file, &imports, &exports, |_| None);

        // Container should be resolved
        assert!(
            resolutions.contains_key(&container_node_id),
            "Container in ScopedAccess LHS should have resolution"
        );
        assert_eq!(
            resolutions.get(&container_node_id),
            Some(&Resolution::Def(DefTarget::Workspace(container_def_id))),
            "Container should resolve to export"
        );

        // 'a should be resolved to TypeParam from impl
        let expected_type_param_id = TypeParamId {
            owner: def_id,
            index: 0,
        };
        assert!(
            resolutions.contains_key(&a_node_id),
            "'a in ScopedAccess LHS should have resolution"
        );
        assert_eq!(
            resolutions.get(&a_node_id),
            Some(&Resolution::TypeParam(expected_type_param_id)),
            "'a should resolve to impl's TypeParam"
        );
    }
}

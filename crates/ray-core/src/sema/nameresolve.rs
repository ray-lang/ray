use std::{collections::HashMap, ops::DerefMut};

use ray_shared::{
    collections::{namecontext::NameContext, nametree::Scope},
    def::DefId,
    local_binding::LocalBindingId,
    node_id::NodeId,
    pathlib::{ModulePath, Path},
    resolution::{DefTarget, Resolution},
    span::{Sourced, parsed::Parsed},
    ty::Ty,
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

/// Resolve names in a file AST and return the resolution table.
///
/// This is a pure function that walks the AST read-only and returns a mapping
/// from NodeIds to their resolutions without mutating the input.
///
/// Parameters:
/// - `ast`: The parsed file AST
/// - `imports`: Map from import alias to module path. For `import std::io`,
///   the key is "io" and the value is the module path.
/// - `module_exports`: Exports from the current file's module (same-module definitions)
/// - `sibling_exports`: Exports from sibling files in the same module
/// - `import_exports`: Callback to get exports for an imported module by alias
pub fn resolve_names_in_file(
    ast: &File,
    imports: &HashMap<String, ModulePath>,
    module_exports: &HashMap<String, DefTarget>,
    sibling_exports: &HashMap<String, DefTarget>,
    import_exports: impl Fn(&str) -> Option<HashMap<String, DefTarget>>,
) -> HashMap<NodeId, Resolution> {
    let mut resolutions = HashMap::new();
    let mut local_scopes: Vec<HashMap<String, LocalBindingId>> = vec![HashMap::new()];
    let mut current_def: Option<DefId> = None;
    let mut local_counter: u32 = 0;

    for item in walk_file(ast) {
        match item {
            WalkItem::EnterScope(WalkScopeKind::Function) => {
                local_scopes.push(HashMap::new());
            }
            WalkItem::EnterScope(WalkScopeKind::Closure | WalkScopeKind::Block) => {
                local_scopes.push(HashMap::new());
            }
            WalkItem::ExitScope(_) => {
                local_scopes.pop();
            }
            WalkItem::Decl(decl) => {
                if let Decl::Func(func) = &decl.value {
                    current_def = Some(decl.id.owner);
                    local_counter = 0;
                    // Bind function parameters
                    for param in &func.sig.params {
                        if let Some(name) = param.value.name().name() {
                            if let Some(owner) = current_def {
                                let local_id = LocalBindingId::new(owner, local_counter);
                                local_counter += 1;
                                if let Some(scope) = local_scopes.last_mut() {
                                    scope.insert(name, local_id);
                                }
                                resolutions.insert(param.id, Resolution::Local(local_id));
                            }
                        }
                    }
                } else if let Decl::Impl(imp) = &decl.value {
                    // Resolve type references in impl block
                    // For `impl ToStr[Point]`, resolve the trait type (ToStr)
                    resolve_impl_type_refs(
                        imp,
                        imports,
                        module_exports,
                        sibling_exports,
                        &import_exports,
                        &mut resolutions,
                    );
                }
            }
            WalkItem::Func(func) => {
                // This is emitted for impl methods
                current_def = Some(func.id.owner);
                local_counter = 0;
                // Bind function parameters
                for param in &func.sig.params {
                    if let Some(name) = param.value.name().name() {
                        if let Some(owner) = current_def {
                            let local_id = LocalBindingId::new(owner, local_counter);
                            local_counter += 1;
                            if let Some(scope) = local_scopes.last_mut() {
                                scope.insert(name, local_id);
                            }
                            resolutions.insert(param.id, Resolution::Local(local_id));
                        }
                    }
                }
            }
            WalkItem::Expr(expr) => {
                match &expr.value {
                    Expr::Name(name) => {
                        let name_str = name.path.name().unwrap_or_default();
                        // Check locals first
                        let resolution = lookup_local(&local_scopes, &name_str)
                            .map(Resolution::Local)
                            .or_else(|| {
                                lookup_def(module_exports, sibling_exports, &name_str)
                                    .map(Resolution::Def)
                            });
                        if let Some(res) = resolution {
                            resolutions.insert(expr.id, res);
                        }
                    }
                    Expr::Path(path) if path.len() == 1 => {
                        let name_str = path.name().unwrap_or_default();
                        let resolution = lookup_local(&local_scopes, &name_str)
                            .map(Resolution::Local)
                            .or_else(|| {
                                lookup_def(module_exports, sibling_exports, &name_str)
                                    .map(Resolution::Def)
                            });
                        if let Some(res) = resolution {
                            resolutions.insert(expr.id, res);
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
                                    let second_segment = name_vec.get(1).cloned().unwrap_or_default();
                                    if let Some(target) = imported_exports.get(&second_segment) {
                                        resolutions.insert(expr.id, Resolution::Def(target.clone()));
                                    }
                                }
                            }
                        }
                    }
                    Expr::Closure(closure) => {
                        // Bind closure parameters
                        for arg in &closure.args.items {
                            if let Expr::Name(name) = &arg.value {
                                if let Some(n) = name.path.name() {
                                    if let Some(owner) = current_def {
                                        let local_id = LocalBindingId::new(owner, local_counter);
                                        local_counter += 1;
                                        if let Some(scope) = local_scopes.last_mut() {
                                            scope.insert(n, local_id);
                                        }
                                        resolutions.insert(arg.id, Resolution::Local(local_id));
                                    }
                                }
                            }
                        }
                    }
                    Expr::Curly(curly) => {
                        // Resolve the struct type name for curly expressions like `Point { x, y }`
                        // The resolution is stored on the Curly expression's NodeId
                        if let Some(parsed_path) = &curly.lhs {
                            if let Some(name_str) = parsed_path.name() {
                                // Look up the struct in module exports
                                if let Some(target) =
                                    lookup_def(module_exports, sibling_exports, &name_str)
                                {
                                    resolutions.insert(expr.id, Resolution::Def(target));
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            WalkItem::Pattern(pat) => {
                // Handle assignment patterns that introduce new bindings
                for node in pat.paths() {
                    let (path, is_lvalue) = node.value;
                    if !is_lvalue {
                        if let Some(name) = path.name() {
                            if let Some(owner) = current_def {
                                let local_id = LocalBindingId::new(owner, local_counter);
                                local_counter += 1;
                                if let Some(scope) = local_scopes.last_mut() {
                                    scope.insert(name, local_id);
                                }
                                resolutions.insert(node.id, Resolution::Local(local_id));
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    resolutions
}

fn lookup_local(scopes: &[HashMap<String, LocalBindingId>], name: &str) -> Option<LocalBindingId> {
    for scope in scopes.iter().rev() {
        if let Some(&local_id) = scope.get(name) {
            return Some(local_id);
        }
    }
    None
}

fn lookup_def(
    module_exports: &HashMap<String, DefTarget>,
    sibling_exports: &HashMap<String, DefTarget>,
    name: &str,
) -> Option<DefTarget> {
    module_exports
        .get(name)
        .or_else(|| sibling_exports.get(name))
        .cloned()
}

/// Resolve type references in an impl block.
///
/// For `impl ToStr[Point]`, this resolves:
/// - The trait type `ToStr` (first synthetic_id)
/// - The implementing type `Point` (second synthetic_id, if present)
///
/// For `impl object Point`, there's no trait to resolve.
fn resolve_impl_type_refs(
    imp: &Impl,
    imports: &HashMap<String, ModulePath>,
    module_exports: &HashMap<String, DefTarget>,
    sibling_exports: &HashMap<String, DefTarget>,
    import_exports: &impl Fn(&str) -> Option<HashMap<String, DefTarget>>,
    resolutions: &mut HashMap<NodeId, Resolution>,
) {
    // Get the synthetic IDs for this impl's type
    let synth_ids = imp.ty.synthetic_ids();

    // For trait impls like `impl ToStr[Point]`:
    // - imp.is_object is false
    // - imp.ty is Ty::Proj(trait_path, [implementing_type, ...])
    // - synth_ids[0] is the NodeId for the trait type (ToStr)
    // - synth_ids[1] is the NodeId for the implementing type (Point)
    //
    // For inherent impls like `impl object Point`:
    // - imp.is_object is true
    // - imp.ty is the implementing type directly
    // - synth_ids[0] is the NodeId for the implementing type
    if imp.is_object {
        // Inherent impl: resolve the implementing type directly
        // imp.ty is something like Ty::Const(Point) or Ty::Proj(Point, [...])
        let implementing_type_path = imp.ty.get_path();
        if let Some(type_name) = implementing_type_path.name() {
            let resolution = resolve_type_name(
                &type_name,
                &implementing_type_path,
                imports,
                module_exports,
                sibling_exports,
                import_exports,
            );

            if let Some(target) = resolution {
                if let Some(node_id) = synth_ids.first() {
                    resolutions.insert(*node_id, Resolution::Def(target));
                }
            }
        }
    } else {
        // Trait impl: resolve both the trait and the implementing type
        if let Ty::Proj(trait_path, args) = &*imp.ty {
            // Resolve the trait (first synthetic_id)
            if let Some(trait_name) = trait_path.name() {
                let resolution = resolve_type_name(
                    &trait_name,
                    trait_path,
                    imports,
                    module_exports,
                    sibling_exports,
                    import_exports,
                );

                if let Some(target) = resolution {
                    if let Some(node_id) = synth_ids.first() {
                        resolutions.insert(*node_id, Resolution::Def(target));
                    }
                }
            }

            // Resolve the implementing type (second synthetic_id, from first type arg)
            if let Some(implementing_ty) = args.first() {
                let implementing_type_path = implementing_ty.get_path();
                if let Some(type_name) = implementing_type_path.name() {
                    let resolution = resolve_type_name(
                        &type_name,
                        &implementing_type_path,
                        imports,
                        module_exports,
                        sibling_exports,
                        import_exports,
                    );

                    if let Some(target) = resolution {
                        if let Some(node_id) = synth_ids.get(1) {
                            resolutions.insert(*node_id, Resolution::Def(target));
                        }
                    }
                }
            }
        }
    }
}

/// Resolve a type name to a DefTarget.
///
/// Checks in order:
/// 1. Module exports (same module definitions)
/// 2. Sibling exports (same module, different file)
/// 3. Imported modules (qualified paths like `io::Foo` or selective imports)
fn resolve_type_name(
    name: &str,
    path: &Path,
    imports: &HashMap<String, ModulePath>,
    module_exports: &HashMap<String, DefTarget>,
    sibling_exports: &HashMap<String, DefTarget>,
    import_exports: &impl Fn(&str) -> Option<HashMap<String, DefTarget>>,
) -> Option<DefTarget> {
    let name_vec = path.to_name_vec();

    // If it's a simple name (single segment), check module/sibling exports first
    if name_vec.len() == 1 {
        if let Some(target) = lookup_def(module_exports, sibling_exports, name) {
            return Some(target);
        }
    }

    // If it's a qualified path (multiple segments), try to resolve via imports
    if name_vec.len() >= 2 {
        let first_segment = &name_vec[0];
        if imports.contains_key(first_segment) {
            if let Some(imported_exports) = import_exports(first_segment) {
                // For now, only handle two-segment paths like `io::Foo`
                if name_vec.len() == 2 {
                    let second_segment = &name_vec[1];
                    if let Some(target) = imported_exports.get(second_segment) {
                        return Some(target.clone());
                    }
                }
            }
        }
    }

    None
}

// ============================================================================
// Legacy name resolution (mutating AST)
// ============================================================================

pub struct ResolveContext<'a> {
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

impl<'a> ResolveContext<'a> {
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
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()>;
}

impl NameResolve for Sourced<'_, Name> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
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
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
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
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
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
        }
    }
}

impl NameResolve for Node<Expr> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
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
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
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
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
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
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.as_mut().resolve_names(ctx)
    }
}

impl<T> NameResolve for Vec<T>
where
    T: NameResolve,
{
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        for el in self {
            el.resolve_names(ctx)?;
        }

        Ok(())
    }
}

impl NameResolve for Module<(), Decl> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
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
                        for func_node in funcs {
                            let func_def_id = func_node.id.owner;
                            ctx.resolve_func_body(func_def_id, &mut func_node.value)?;
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
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
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
            Decl::Func(_) | Decl::Trait(_) | Decl::TypeAlias(_, _) | Decl::Extern(_) => {
                unreachable!("extern cannot wrap {:?}", ext.decl())
            }
        }

        Ok(())
    }
}

impl NameResolve for Sourced<'_, Func> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (func, src) = self.unpack_mut();
        // note: we're only processing the signature here and not the body
        Sourced(&mut func.sig, src).resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, FuncSig> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (sig, _) = self.unpack_mut();
        ctx.add_path(&sig.path);
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Struct> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (st, _) = self.unpack_mut();
        let name = st.path.name().unwrap();
        if !Ty::is_builtin_name(&name) {
            ctx.add_path(&st.path);
        }

        Ok(())
    }
}

impl NameResolve for Sourced<'_, Trait> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
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
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (imp, src) = self.unpack_mut();
        if let Some(funcs) = &mut imp.funcs {
            for func in funcs {
                log::debug!("resolve_names: impl func: {:?}", func.sig);
                Sourced(&mut func.sig, src).resolve_names(ctx)?;
            }
        }

        Ok(())
    }
}

impl NameResolve for Sourced<'_, Expr> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
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
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Assign> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (assign, src) = self.unpack_mut();
        for node in assign.lhs.paths_mut() {
            let (path, is_lvalue) = node.value;
            let base_scope = ctx.current_scope_or(&src.path.with_names_only());
            let name_str = path.name();
            let full_path = base_scope.append_path(path.clone());
            *path = full_path.clone();

            if !is_lvalue {
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
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)?;
        self.rhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Block> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.stmts.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Boxed> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.inner.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Call> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.callee.resolve_names(ctx)?;
        self.args.items.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Cast> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Closure> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
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
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.elements.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Dict> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        for (key, value) in self.entries.iter_mut() {
            key.resolve_names(ctx)?;
            value.resolve_names(ctx)?;
        }
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Set> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.items.resolve_names(ctx)
    }
}

impl NameResolve for Node<CurlyElement> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        match &mut self.value {
            CurlyElement::Name(n) => Sourced(n, &src).resolve_names(ctx),
            CurlyElement::Labeled(_, rhs) => rhs.resolve_names(ctx),
        }
    }
}

impl NameResolve for Sourced<'_, Deref> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.expr.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Dot> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, For> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
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
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.cond.resolve_names(ctx)?;
        self.then.resolve_names(ctx)?;
        self.els.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Index> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)?;
        self.index.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, List> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.items.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Literal> {
    fn resolve_names(&mut self, _: &mut ResolveContext) -> RayResult<()> {
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Loop> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.body.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, New> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        if let Some(count) = &mut self.count {
            count.resolve_names(ctx)?
        }
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Pattern> {
    fn resolve_names(&mut self, _: &mut ResolveContext) -> RayResult<()> {
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Range> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.start.resolve_names(ctx)?;
        self.end.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Ref> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.expr.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Sequence> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.items.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Tuple> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.seq.items.resolve_names(ctx)
    }
}

impl NameResolve for Parsed<TyScheme> {
    fn resolve_names(&mut self, _: &mut ResolveContext) -> RayResult<()> {
        Ok(())
    }
}

impl NameResolve for Sourced<'_, UnaryOp> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.expr.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, While> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.cond.resolve_names(ctx)?;
        self.body.resolve_names(ctx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        Assign, Block, Closure as AstClosure, Decl, Expr, Func, Literal, Name, Node,
        Pattern as AstPattern, Sequence,
    };
    use ray_shared::def::DefId;
    use ray_shared::file_id::FileId;
    use ray_shared::node_id::NodeId;
    use ray_shared::pathlib::{FilePath, Path};
    use ray_shared::span::Span;

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
        let module_exports = HashMap::new();
        let sibling_exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &module_exports, &sibling_exports, |_| None);

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
        let mut module_exports = HashMap::new();
        let foo_def_id = DefId::new(FileId(0), 1);
        module_exports.insert("foo".to_string(), DefTarget::Workspace(foo_def_id));
        let sibling_exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &module_exports, &sibling_exports, |_| None);

        // Body name should resolve to the module export
        assert!(resolutions.contains_key(&body_name.id));
        let body_res = resolutions.get(&body_name.id).unwrap();
        assert!(matches!(body_res, Resolution::Def(DefTarget::Workspace(id)) if *id == foo_def_id));
    }

    #[test]
    fn resolve_names_in_file_resolves_sibling_export() {
        // fn f() { bar }  where bar is in sibling_exports
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
        let module_exports = HashMap::new();
        let mut sibling_exports = HashMap::new();
        let bar_def_id = DefId::new(FileId(0), 2);
        sibling_exports.insert("bar".to_string(), DefTarget::Workspace(bar_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &module_exports, &sibling_exports, |_| None);

        // Body name should resolve to the sibling export
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
        let mut module_exports = HashMap::new();
        let x_def_id = DefId::new(FileId(0), 1);
        module_exports.insert("x".to_string(), DefTarget::Workspace(x_def_id));
        let sibling_exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &module_exports, &sibling_exports, |_| None);

        // Body name should resolve to local, not module export
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
        let module_exports = HashMap::new();
        let sibling_exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &module_exports, &sibling_exports, |_| None);

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
        let module_exports = HashMap::new();
        let sibling_exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &module_exports, &sibling_exports, |_| None);

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
    fn resolve_names_in_file_module_export_prefers_over_sibling() {
        // When same name in both module_exports and sibling_exports, module wins
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        let body_name = Node::new(Expr::Name(Name::new("shared")));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![body_name.clone()],
        }));
        let func = Func::new(Node::new(Path::from("test::f")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let file = test_file(vec![decl], vec![]);
        let imports = HashMap::new();
        let mut module_exports = HashMap::new();
        let module_def_id = DefId::new(FileId(0), 1);
        module_exports.insert("shared".to_string(), DefTarget::Workspace(module_def_id));
        let mut sibling_exports = HashMap::new();
        let sibling_def_id = DefId::new(FileId(0), 2);
        sibling_exports.insert("shared".to_string(), DefTarget::Workspace(sibling_def_id));

        let resolutions = resolve_names_in_file(&file, &imports, &module_exports, &sibling_exports, |_| None);

        // Body name should resolve to module export, not sibling
        assert!(resolutions.contains_key(&body_name.id));
        let body_res = resolutions.get(&body_name.id).unwrap();
        assert!(
            matches!(body_res, Resolution::Def(DefTarget::Workspace(id)) if *id == module_def_id)
        );
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
        let module_exports = HashMap::new();
        let sibling_exports = HashMap::new();

        let resolutions = resolve_names_in_file(&file, &imports, &module_exports, &sibling_exports, |_| None);

        // Unknown name should not be in the resolution map
        assert!(!resolutions.contains_key(&body_name.id));
    }

    #[test]
    fn resolve_names_in_file_resolves_curly_struct_type() {
        // fn f() { Point { x: 1 } }  where Point is a struct export
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);

        use crate::ast::{Curly, CurlyElement};
        use ray_shared::span::{Source, parsed::Parsed};

        // Create curly expression: Point { x: 1 }
        let field_name = Name::new("x");
        let field_value = Node::new(Expr::Name(Name::new("dummy")));
        let curly_elem = Node::new(CurlyElement::Labeled(field_name, field_value));
        let curly_expr = Node::new(Expr::Curly(Curly {
            lhs: Some(Parsed::new(Path::from("Point"), Source::default())),
            elements: vec![curly_elem],
            curly_span: ray_shared::span::Span::default(),
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
        let mut module_exports = HashMap::new();
        module_exports.insert(
            "Point".to_string(),
            DefTarget::Workspace(point_def_id),
        );
        let sibling_exports = HashMap::new();

        let resolutions =
            resolve_names_in_file(&file, &imports, &module_exports, &sibling_exports, |_| None);

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
}

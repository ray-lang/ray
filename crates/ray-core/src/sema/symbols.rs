use std::collections::{HashMap, HashSet};

use ray_shared::{
    node_id::NodeId,
    pathlib::{FilePath, Path},
    span::{Source, Span, parsed::Parsed},
    ty::Ty,
};
use ray_typing::{tyctx::TyCtx, types::TyScheme};

use crate::{
    ast::{
        Assign, Call, Curly, CurlyElement, Decl, Dot, Expr, Func, FuncSig, Module, ScopedAccess,
        WalkItem, walk_module,
    },
    sourcemap::SourceMap,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolRole {
    Definition,
    Reference,
}

#[derive(Debug, Clone)]
pub struct SymbolTarget {
    pub path: Path,
    pub filepath: FilePath,
    pub span: Span,
    pub role: SymbolRole,
}

#[derive(Debug, Default, Clone)]
pub struct SymbolMap {
    entries: HashMap<NodeId, Vec<SymbolTarget>>,
}

impl SymbolMap {
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn insert(&mut self, node_id: NodeId, target: SymbolTarget) {
        self.entries.entry(node_id).or_default().push(target);
    }

    pub fn get(&self, node_id: &NodeId) -> Option<&[SymbolTarget]> {
        self.entries.get(node_id).map(|targets| targets.as_slice())
    }

    pub fn iter(&self) -> impl Iterator<Item = (NodeId, &SymbolTarget)> {
        self.entries.iter().flat_map(|(id, targets)| {
            let id = *id;
            targets.iter().map(move |target| (id, target))
        })
    }
}

pub struct SymbolBuildContext<'a> {
    module: &'a Module<(), Decl>,
    tcx: &'a TyCtx,
    srcmap: &'a SourceMap,
    symbol_map: SymbolMap,
    definitions: HashMap<Path, SymbolTarget>,
    struct_fields: HashMap<(String, String), Path>,
    references: Vec<(NodeId, Path)>,
    ignore: HashSet<NodeId>,
}

impl<'a> SymbolBuildContext<'a> {
    pub fn new(
        module: &'a Module<(), Decl>,
        tcx: &'a TyCtx,
        srcmap: &'a SourceMap,
    ) -> SymbolBuildContext<'a> {
        SymbolBuildContext {
            module,
            tcx,
            srcmap,
            symbol_map: SymbolMap::new(),
            definitions: HashMap::new(),
            struct_fields: HashMap::new(),
            references: Vec::new(),
            ignore: HashSet::new(),
        }
    }

    fn record_definition(&mut self, node_id: NodeId, path: &Path, source: &Source) {
        if path.is_empty() {
            return;
        }

        let Some(span) = source.span else {
            return;
        };

        let target = SymbolTarget {
            path: path.clone(),
            filepath: source.filepath.clone(),
            span,
            role: SymbolRole::Definition,
        };

        log::debug!("[record definition] node_id={}, path={}", node_id, path);
        self.symbol_map.insert(node_id, target.clone());
        self.definitions.insert(path.clone(), target);
    }

    fn record_reference(&mut self, node_id: NodeId, path: &Path) {
        if self.ignore.contains(&node_id) {
            log::debug!(
                "[record reference] IGNORE node_id={}, path={}",
                node_id,
                path
            );
            return;
        }

        log::debug!("[record reference] node_id={}, path={}", node_id, path);
        self.references.push((node_id, path.clone()));
    }

    fn record_assign(&mut self, assign: &Assign) {
        for node in assign.lhs.paths() {
            let (path, is_lvalue) = node.value;
            if !is_lvalue {
                let source = self.srcmap.get_by_id(node.id).unwrap();
                self.record_definition(node.id, &path, &source);
            } else {
                self.record_reference(node.id, &path);
            }
        }
    }

    fn record_func_sig(&mut self, sig: &FuncSig) {
        if let Some(sig_source) = self.srcmap.get_by_id(sig.path.id) {
            self.record_definition(sig.path.id, &sig.path, &sig_source);
        }

        for param in sig.params.iter() {
            if let Some(param_source) = self.srcmap.get_by_id(param.id) {
                self.record_definition(param.id, param.name(), &param_source);
            }

            if let Some(parsed_ty) = param.parsed_ty() {
                log::debug!(
                    "[record_func_sig] recording parsed type for param: {:?}",
                    param
                );
                self.record_parsed_scheme(parsed_ty);
            }
        }
    }

    fn record_struct_literal(&mut self, curly: &Curly) {
        let Some(lhs) = &curly.lhs else {
            return;
        };

        let struct_path = lhs.value().clone();
        let struct_name = struct_path
            .name()
            .unwrap_or_else(|| struct_path.to_string());

        for element in &curly.elements {
            if let CurlyElement::Labeled(field_name, expr) = &element.value {
                let field_ident = field_name
                    .path
                    .name()
                    .unwrap_or_else(|| field_name.path.to_string());

                if let Some(field_path) = self
                    .struct_fields
                    .get(&(struct_name.clone(), field_ident.clone()))
                {
                    let field_path = field_path.clone();
                    self.record_reference(expr.id, &field_path);
                } else {
                    let fallback_path = struct_path.append(field_ident);
                    self.record_reference(expr.id, &fallback_path);
                }
            }
        }
    }

    fn record_call(&mut self, call: &Call) {
        let call_id = call.call_resolution_id();
        if let Some(resolved) = self.tcx.call_resolution(call_id) {
            let trait_path = &resolved.base_fqn;
            // Always record a reference to the (possibly polymorphic) trait method.
            self.record_reference(call_id, trait_path);

            // Also record a reference to the fully-instantiated impl FQN by
            // mirroring the method resolution logic used in LIR generation.
            let callee_expr_id = call.callee.id;
            let arg_ids: Vec<NodeId> = call.args.items.iter().map(|arg| arg.id).collect();
            let impl_path = self.tcx.resolve_method_impl_fqn(
                trait_path.clone(),
                call_id,
                callee_expr_id,
                &arg_ids,
            );

            self.record_reference(call_id, &impl_path);
        }
    }

    fn record_dot(&mut self, dot: &Dot) {
        let lhs_ty = self.tcx.ty_of(dot.lhs.id);
        let mut fqn = match lhs_ty.mono() {
            Ty::Ref(ty) => ty.get_path(),
            ty => ty.get_path(),
        };

        fqn.append_mut(dot.rhs.path.to_short_name());
        self.record_reference(dot.rhs.id, &fqn.with_names_only());
        self.ignore.insert(dot.rhs.id);
    }

    fn record_scoped_access(&mut self, scoped_access: &ScopedAccess) {
        let Expr::Type(ty) = &scoped_access.lhs.value else {
            return;
        };
        let base = ty.value().mono().get_path().without_type_args();
        let member = scoped_access
            .rhs
            .value
            .path
            .name()
            .unwrap_or_else(|| scoped_access.rhs.value.to_string());
        let path = base.append(member);
        self.record_reference(scoped_access.rhs.id, &path);
        self.ignore.insert(scoped_access.rhs.id);
    }

    fn record_parsed_ty(&mut self, parsed_ty: &Parsed<Ty>) {
        let ids = parsed_ty.synthetic_ids();
        let tys = parsed_ty.flatten();
        if ids.len() != tys.len() {
            log::debug!(
                "[record_parsed_ty] mismatched number of ids vs types: {:?} and {:?}",
                ids,
                tys
            );
        }

        for (id, ty) in ids.iter().zip(tys.iter()) {
            let path = ty.get_path().with_names_only();
            self.record_reference(*id, &path);
        }
    }

    fn record_parsed_scheme(&mut self, parsed_ty: &Parsed<TyScheme>) {
        let ids = parsed_ty.synthetic_ids();
        let tys = parsed_ty.mono().flatten();
        if ids.len() != tys.len() {
            log::debug!(
                "[record_parsed_scheme] mismatched number of ids vs types from scheme {:?}: {:?} and {:?}",
                parsed_ty,
                ids,
                tys
            );
        }

        for (id, ty) in ids.iter().zip(tys.iter()) {
            let path = ty.get_path().with_names_only();
            self.record_reference(*id, &path);
        }
    }

    fn collect_from_module(&mut self) {
        for item in walk_module(self.module) {
            log::debug!("[build_symbol_map] item = {:?}", item);
            match item {
                WalkItem::Decl(decl) => match &decl.value {
                    Decl::Mutable(node) | Decl::Name(node) => {
                        if let Some(source) = self.srcmap.get_by_id(node.id) {
                            self.record_definition(node.id, &node.path, &source);
                        }
                    }
                    Decl::Trait(tr) => {
                        let trait_src = self.srcmap.get(&tr.path);
                        self.record_definition(tr.path.id, &tr.path, &trait_src);
                    }
                    Decl::Struct(st) => {
                        let struct_path = st.path.value.clone();
                        let struct_name = struct_path.name().unwrap();
                        if !Ty::is_builtin_name(&struct_name) {
                            let name_src = self.srcmap.get(&st.path);
                            self.record_definition(st.path.id, &struct_path, &name_src);
                        }

                        if let Some(fields) = &st.fields {
                            for field in fields {
                                let field_source = self.srcmap.get(field);
                                let field_name = field
                                    .value
                                    .path
                                    .name()
                                    .unwrap_or_else(|| field.value.path.to_string());
                                let field_path = struct_path.append(field_name.clone());
                                self.record_definition(field.id, &field_path, &field_source);
                                self.struct_fields
                                    .insert((struct_name.to_string(), field_name), field_path);
                            }
                        }
                    }
                    Decl::Func(Func { sig, .. }) | Decl::FnSig(sig) => {
                        self.record_func_sig(sig);
                    }
                    Decl::Declare(assign) => self.record_assign(assign),
                    Decl::Impl(imp) => {
                        self.record_parsed_ty(&imp.ty);
                    }
                    Decl::Extern(_) | Decl::TypeAlias(_, _) => continue,
                },
                WalkItem::Expr(expr) => match &expr.value {
                    Expr::Assign(assign) => self.record_assign(assign),
                    Expr::Call(call) => self.record_call(call),
                    Expr::Curly(curly) => self.record_struct_literal(curly),
                    Expr::Dot(dot) => self.record_dot(dot),
                    Expr::Func(func) => self.record_func_sig(&func.sig),
                    Expr::Name(name) => {
                        self.record_reference(expr.id, &name.path);
                    }
                    Expr::Path(path) => {
                        self.record_reference(expr.id, path);
                    }
                    Expr::ScopedAccess(scoped_access) => self.record_scoped_access(scoped_access),
                    _ => continue,
                },
                WalkItem::Func(func) => {
                    self.record_func_sig(&func.sig);
                }
                WalkItem::Name(node) => {
                    self.record_reference(node.id, &node.path);
                }
                WalkItem::CurlyElement(element) => match &element.value {
                    CurlyElement::Name(name) => {
                        self.record_reference(element.id, &name.path);
                    }
                    CurlyElement::Labeled(_, _) => continue,
                },
                _ => continue,
            }
        }
    }

    fn resolve_references(&mut self) {
        while let Some((node_id, path)) = self.references.pop() {
            if let Some(targets) = self.symbol_map.get(&node_id) {
                if targets.iter().any(|existing| {
                    existing.path == path && matches!(existing.role, SymbolRole::Reference)
                }) {
                    log::debug!(
                        "[record reference] targets already contain path as reference: node_id={}, path={}",
                        node_id,
                        path
                    );
                    continue;
                }
            }

            if let Some(target) = self.definitions.get(&path) {
                let mut target = target.clone();
                target.role = SymbolRole::Reference;
                log::debug!(
                    "[record reference] inserting: node_id={}, path={}",
                    node_id,
                    path
                );
                self.symbol_map.insert(node_id, target);
            } else {
                log::debug!(
                    "[record reference] FAILED to find path in definitions: node_id={}, path={}",
                    node_id,
                    path
                );
            }
        }
    }
}

pub fn build_symbol_map(mut ctx: SymbolBuildContext<'_>) -> SymbolMap {
    ctx.collect_from_module();
    ctx.resolve_references();
    ctx.symbol_map
}

use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap, HashSet},
    ops::Deref,
    rc::Rc,
};

use ray_lir::START_FUNCTION;
use ray_shared::{
    def::{DefId, DefKind},
    file_id::FileId,
    local_binding::LocalBindingId,
    node_id::NodeId,
    pathlib::{ItemPath, ModulePath, Path},
    resolution::{DefTarget, Resolution},
    span::Source,
    ty::Ty,
};
use ray_typing::{
    call_resolution::CallResolution,
    types::{
        ImplKind, ImplTy, NominalKind, ReceiverMode, StructTy, Subst, Substitutable, TyScheme,
    },
    unify::{match_ty, mgu},
};

use ray_core::{
    ast::{
        self, Assign, Call, Closure, CurlyElement, Decl, Expr, FStringPart, Literal, Modifier,
        Node, Pattern, PrefixOp, RangeLimits, token::IntegerBase,
    },
    errors::{RayError, RayErrorKind, RayResult},
    sema::closure::ClosureInfo,
    sourcemap::SourceMap,
};
use ray_frontend::{
    queries::{
        bindings::local_binding_for_node,
        calls::call_resolution,
        closures::closure_info,
        defs::{
            def_for_path, def_path, definition_record, impl_def, impls_for_trait,
            method_receiver_mode, struct_def, trait_def,
        },
        libraries::{LoadedLibraries, library_lir},
        parse::parse_file,
        resolve::{name_resolutions, resolve_builtin},
        transform::file_ast,
        typecheck::{def_scheme, inferred_local_type, ty_of},
        types::resolved_ty,
        workspace::WorkspaceSnapshot,
    },
    query::Database,
};
use ray_lir as lir;

use crate::{lir::Builder, mangle, mono};

/// Generate LIR for the workspace.
///
/// This is the main entry point for LIR generation. It processes all files
/// in the workspace and generates a single LIR program.
///
/// # Arguments
/// * `db` - The query database
/// * `is_lib` - Whether we're building a library (skips _start generation)
pub fn generate(db: &Database, is_lib: bool) -> RayResult<lir::Program> {
    // Get workspace and libraries
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let libraries = db.get_input::<LoadedLibraries>(());
    let libs: Vec<lir::Program> = libraries
        .all_library_roots()
        .filter_map(|lib_root| library_lir(db, lib_root.clone()))
        .collect();

    // Get entry file and module path
    let entry_file_id = workspace.entry.ok_or_else(|| RayError {
        msg: "no entry file in workspace".to_string(),
        src: vec![],
        kind: RayErrorKind::Compile,
        context: None,
    })?;
    let entry_info = workspace.file_info(entry_file_id).ok_or_else(|| RayError {
        msg: "entry file not found in workspace".to_string(),
        src: vec![],
        kind: RayErrorKind::Compile,
        context: None,
    })?;
    let path = entry_info.module_path.to_path();

    // Build combined SourceMap and collect all decls from all files.
    // Extern declarations are collected separately so they can be registered
    // before any function bodies are generated (which may reference them).
    let mut combined_srcmap = SourceMap::new();
    let mut extern_decls: Vec<Node<Decl>> = Vec::new();
    let mut all_decls: Vec<Node<Decl>> = Vec::new();

    for file_id in workspace.all_file_ids() {
        let file_ast_result = file_ast(db, file_id);
        combined_srcmap.extend_with(file_ast_result.source_map.clone());
        for decl in file_ast_result.ast.decls.clone() {
            match &decl.value {
                Decl::FnSig(sig) if sig.modifiers.contains(&Modifier::Extern) => {
                    extern_decls.push(decl);
                }
                Decl::Mutable(_, m) | Decl::Name(_, m) if m.contains(&Modifier::Extern) => {
                    extern_decls.push(decl);
                }
                _ => all_decls.push(decl),
            }
        }
    }

    // Find user main function
    let user_main_info = resolve_user_main_info(db, &path);

    // Create program and generate LIR for all decls
    let prog = Rc::new(RefCell::new(lir::Program::new(path)));
    let mut ctx = GenCtx::new(db, entry_file_id, Rc::clone(&prog), &combined_srcmap);
    extern_decls.lir_gen(&mut ctx)?;
    all_decls.lir_gen(&mut ctx)?;

    let (module_main_path, user_main_base_path) = {
        let prog_ref = prog.borrow();
        (
            prog_ref.module_main_path(),
            prog_ref.module_path.to_path().append("main"),
        )
    };

    let has_module_main = {
        let prog_ref = prog.borrow();
        prog_ref.funcs.iter().any(|f| f.name == module_main_path)
    };

    if !has_module_main {
        // Enter a synthetic def scope for LIR-generated nodes
        let _guard = NodeId::enter_def(DefId::default());

        ctx.with_builder(Builder::new());
        ctx.with_new_block(|ctx| {
            ctx.ret(lir::Value::Empty);
        });

        let builder = ctx.builder.take().unwrap();
        let (params, locals, blocks, symbols, cfg) = builder.done();
        let mut module_main_fn = lir::Func::new(
            module_main_path.clone(),
            TyScheme::from_mono(Ty::Func(vec![], Box::new(Ty::unit()))),
            vec![],
            symbols,
            cfg,
            None, // synthetic function
        );
        module_main_fn.params = params;
        module_main_fn.locals = locals;
        module_main_fn.blocks = blocks;
        ctx.new_func(module_main_fn);
    }

    let user_main_resolved_path = if let Some((path, _)) = &user_main_info {
        Some(path.clone())
    } else {
        let prog_ref = prog.borrow();
        prog_ref.funcs.iter().find_map(|f| {
            f.name
                .starts_with(&user_main_base_path)
                .then(|| f.name.clone())
        })
    };

    let start_idx = if !is_lib {
        let mut main_symbols = lir::SymbolSet::new();
        log::debug!("module main path: {}", module_main_path);
        if let Some(user_main_resolved_path) = &user_main_resolved_path {
            log::debug!("user main path (resolved): {}", user_main_resolved_path);
        } else {
            log::debug!("user main path (resolved): None");
        }

        ctx.with_builder(Builder::new());
        ctx.with_new_block(|ctx| {
            // call all the main functions from the libs first
            let mut main_funcs = libs
                .iter()
                .map(|l| l.module_main_path())
                .collect::<Vec<_>>();

            // then call _this_ module's main function
            main_funcs.push(module_main_path.clone());

            // generate calls
            for main in main_funcs {
                log::debug!("calling main function: {}", main);
                main_symbols.insert(main.clone());
                ctx.push(
                    lir::Call::new(
                        main,
                        vec![],
                        Ty::Func(vec![], Box::new(Ty::unit())).into(),
                        None,
                    )
                    .into(),
                );
            }

            if let Some((user_main_path, user_main_ty)) = &user_main_info {
                log::debug!("calling user main function: {}", user_main_path);
                main_symbols.insert(user_main_path.clone());
                ctx.push(
                    lir::Call::new(user_main_path.clone(), vec![], user_main_ty.clone(), None)
                        .into(),
                );
            } else if let Some(user_main_path) = &user_main_resolved_path {
                log::debug!("calling user main function: {}", user_main_path);
                main_symbols.insert(user_main_path.clone());
                ctx.push(
                    lir::Call::new(
                        user_main_path.clone(),
                        vec![],
                        Ty::Func(vec![], Box::new(Ty::unit())).into(),
                        None,
                    )
                    .into(),
                );
            }

            ctx.ret(lir::Value::Empty);
        });

        // add the _start function
        let builder = ctx.builder.take().unwrap();
        let (params, locals, blocks, symbols, cfg) = builder.done();
        let mut start_fn = lir::Func::new(
            START_FUNCTION.into(),
            TyScheme::from_mono(Ty::Func(vec![], Box::new(Ty::unit()))),
            vec![],
            symbols,
            cfg,
            None, // synthetic function
        );
        start_fn.params = params;
        start_fn.locals = locals;
        start_fn.blocks = blocks;
        start_fn.symbols.extend(main_symbols);
        ctx.new_func(start_fn) as i64
    } else {
        -1
    };

    // Build struct_types: start with workspace structs, then add synthetic ones
    let mut struct_types = build_struct_types(db);
    for struct_ty in ctx
        .closure_env_types
        .values()
        .chain(ctx.closure_value_types.values())
        .chain(ctx.fn_handle_types.values())
    {
        struct_types.insert(struct_ty.path.clone(), struct_ty.clone());
    }

    drop(ctx);

    // take the prog out of the pointer
    let mut prog = Rc::try_unwrap(prog).unwrap().into_inner();
    prog.start_idx = start_idx;
    prog.resolved_user_main = user_main_resolved_path.clone();
    prog.struct_types = struct_types;
    prog.impls_by_trait = build_impls_by_trait(db);
    if prog.user_main_idx < 0 {
        if let Some(path) = &user_main_resolved_path {
            if let Some(idx) = prog.funcs.iter().position(|f| f.name == *path) {
                prog.user_main_idx = idx as i64;
            }
        }
    }
    for other in libs {
        prog.extend(other);
    }
    Ok(prog)
}

pub fn monomorphize(program: &mut lir::Program) {
    let mut mr = mono::Monomorphizer::new(program);
    let funcs = mr.monomorphize();

    let mono_fn_externs = mr.mono_fn_externs();
    for (poly_fn, mono_fns) in mono_fn_externs {
        let poly_idx = *program.extern_map.get(&poly_fn).unwrap();
        for (mono_fn, mono_ty) in mono_fns {
            let mut mono_ext = program.externs[poly_idx].clone();
            mono_ext.name = mono_fn.clone();
            mono_ext.ty = TyScheme::from_mono(mono_ty);
            program.extern_map.insert(mono_fn, program.externs.len());
            program.externs.push(mono_ext);
        }
    }

    // remove the polymorphic functions
    let module_main_path = program.module_main_path();
    let user_main_base_path = program.module_path.to_path().append("main");
    let resolved_user_main = program.resolved_user_main.clone();
    let mut i = 0;
    while i < program.funcs.len() {
        let f = &program.funcs[i];
        if f.name == START_FUNCTION {
            program.start_idx = i as i64;
        } else if let Some(resolved) = &resolved_user_main {
            if f.name == *resolved {
                program.user_main_idx = i as i64;
            } else if f.name == module_main_path {
                program.module_main_idx = i as i64;
            }
        } else if f.name.starts_with(&user_main_base_path) {
            program.user_main_idx = i as i64;
        } else if f.name == module_main_path {
            program.module_main_idx = i as i64;
        }

        if f.ty.is_polymorphic() {
            program.funcs.remove(i);
        } else {
            i += 1;
        }
    }

    // add the new monomorphized functions
    program.funcs.extend(funcs);
}

/// Build the impls_by_trait map by collecting all trait impls from workspace and libraries.
fn build_impls_by_trait(db: &Database) -> BTreeMap<ItemPath, Vec<ImplTy>> {
    let mut result: BTreeMap<ItemPath, Vec<ImplTy>> = BTreeMap::new();
    let workspace = db.get_input::<WorkspaceSnapshot>(());

    // Collect all trait DefIds from all files in the workspace
    for file_id in workspace.all_file_ids() {
        let parse_result = parse_file(db, file_id);
        for def_header in &parse_result.defs {
            if !matches!(def_header.kind, DefKind::Trait) {
                continue;
            }

            // Get the trait's path
            let trait_target = DefTarget::Workspace(def_header.def_id);
            let Some(trait_path) = def_path(db, trait_target.clone()) else {
                continue;
            };

            // Get all impls for this trait
            let impl_targets = impls_for_trait(db, trait_target);

            let impls: Vec<ImplTy> = impl_targets
                .iter()
                .filter_map(|impl_target| {
                    impl_def(db, impl_target.clone())
                        .deref()
                        .as_ref()
                        .map(|def| def.convert_to_impl_ty())
                })
                .collect();

            if !impls.is_empty() {
                result.entry(trait_path).or_default().extend(impls);
            }
        }
    }

    result
}

/// Build the struct_types map by collecting all struct definitions from workspace and libraries.
fn build_struct_types(db: &Database) -> HashMap<ItemPath, StructTy> {
    let mut result: HashMap<ItemPath, StructTy> = HashMap::new();
    let workspace = db.get_input::<WorkspaceSnapshot>(());

    // Collect all struct DefIds from all files in the workspace
    for file_id in workspace.all_file_ids() {
        let parse_result = parse_file(db, file_id);
        for def_header in &parse_result.defs {
            if !matches!(def_header.kind, DefKind::Struct) {
                continue;
            }

            let target = DefTarget::Workspace(def_header.def_id);
            let Some(struct_definition) = struct_def(db, target) else {
                continue;
            };

            let struct_ty = struct_definition.convert_to_struct_ty();
            result.insert(struct_ty.path.clone(), struct_ty);
        }
    }

    result
}

/// Resolve user main function info from the workspace.
///
/// Searches for a function named `<entry_module>::main` across all files
/// in the workspace and returns its mangled name and type scheme.
fn resolve_user_main_info(db: &Database, entry_module_path: &Path) -> Option<(Path, TyScheme)> {
    let expected = entry_module_path.append("main");
    let workspace = db.get_input::<WorkspaceSnapshot>(());

    for file_id in workspace.all_file_ids() {
        let file_ast_result = file_ast(db, file_id);
        for decl in &file_ast_result.ast.decls {
            if let Decl::Func(func) = &decl.value {
                let func_path = func.sig.path.value.with_names_only();
                if func_path != expected {
                    continue;
                }
                let fn_ty = def_scheme(db, DefTarget::Workspace(decl.id.owner))?;
                let fn_name = if fn_ty.is_polymorphic() {
                    func.sig.path.value.clone()
                } else {
                    mangle::fn_name(&func.sig.path.value, &fn_ty)
                };
                return Some((fn_name, fn_ty));
            }
        }
    }

    None
}

pub trait LirGen<T> {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>) -> RayResult<T>;
}

impl<T, U> LirGen<Vec<U>> for Vec<T>
where
    T: LirGen<U>,
{
    fn lir_gen(&self, ctx: &mut GenCtx<'_>) -> RayResult<Vec<U>> {
        self.iter()
            .map(|t| t.lir_gen(ctx))
            .collect::<RayResult<Vec<_>>>()
    }
}

#[derive(Clone)]
pub struct GenCtx<'a> {
    db: &'a Database,
    file_id: FileId,
    prog: Rc<RefCell<lir::Program>>,
    builder: Option<Builder>,
    data_idx: HashMap<Vec<u8>, usize>,
    global_idx: HashMap<String, usize>,
    pub(crate) srcmap: &'a SourceMap,
    closure_env_types: HashMap<NodeId, StructTy>,
    closure_value_types: HashMap<NodeId, StructTy>,
    closure_fn_types: HashMap<NodeId, TyScheme>,
    closure_funcs: HashMap<NodeId, Path>,
    fn_handle_types: HashMap<(Vec<Ty>, Ty), StructTy>,
    fn_handle_path_types: HashMap<ItemPath, StructTy>,
    fn_handle_wrappers: HashMap<(Path, Vec<Ty>, Ty), Path>,
}

impl<'a> std::ops::Deref for GenCtx<'a> {
    type Target = Builder;

    fn deref(&self) -> &Self::Target {
        self.builder.as_ref().unwrap()
    }
}

impl<'a> std::ops::DerefMut for GenCtx<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.builder.as_mut().unwrap()
    }
}

impl<'a> GenCtx<'a> {
    fn new(
        db: &'a Database,
        file_id: FileId,
        prog: Rc<RefCell<lir::Program>>,
        srcmap: &'a SourceMap,
    ) -> GenCtx<'a> {
        GenCtx {
            db,
            file_id,
            prog,
            builder: None,
            data_idx: HashMap::new(),
            global_idx: HashMap::new(),
            srcmap,
            closure_env_types: HashMap::new(),
            closure_value_types: HashMap::new(),
            closure_fn_types: HashMap::new(),
            closure_funcs: HashMap::new(),
            fn_handle_types: HashMap::new(),
            fn_handle_path_types: HashMap::new(),
            fn_handle_wrappers: HashMap::new(),
        }
    }

    fn ty_of(&mut self, id: NodeId) -> TyScheme {
        let ty = ty_of(self.db, id).unwrap_or_else(|| panic!("could not find type of node {id}"));
        let scheme = TyScheme::from_mono(ty);
        match scheme.mono() {
            Ty::Func(_, _) => {
                // this node appears *as a value* in many contexts; we want
                // the value representation, i.e. FnHandle
                let handle_struct = self.ensure_fn_handle_type(&scheme.mono());
                handle_struct.ty.clone()
            }
            _ => scheme,
        }
    }

    /// Returns the raw type for a node without converting function types to handles.
    /// Use this for function definitions where you need the actual function signature.
    fn raw_ty_of(&self, id: NodeId) -> TyScheme {
        let ty = ty_of(self.db, id).unwrap_or_else(|| panic!("could not find type of node {id}"));
        TyScheme::from_mono(ty)
    }

    fn local_ty_of(&mut self, id: LocalBindingId) -> TyScheme {
        let ty = inferred_local_type(self.db, id)
            .unwrap_or_else(|| panic!("could not find type of node {id}"));
        let scheme = TyScheme::from_mono(ty);
        match scheme.mono() {
            Ty::Func(_, _) => {
                // this node appears *as a value* in many contexts; we want
                // the value representation, i.e. FnHandle
                let handle_struct = self.ensure_fn_handle_type(&scheme.mono());
                handle_struct.ty.clone()
            }
            _ => scheme,
        }
    }

    fn with_builder(&mut self, builder: Builder) -> Option<Builder> {
        self.builder.replace(builder)
    }

    fn path(&self) -> Path {
        self.prog.borrow().module_path.to_path()
    }

    fn add_sym(&mut self, sym: Path) {
        self.builder.as_mut().unwrap().symbols.insert(sym);
    }

    fn new_func(&mut self, func: lir::Func) -> usize {
        let mut prog = self.prog.borrow_mut();
        let idx = prog.funcs.len();
        if func.ty.is_polymorphic() {
            log::debug!("adding function to poly_fn_map: {}", func.name);
            prog.poly_fn_map
                .entry(func.name.clone())
                .or_default()
                .push(idx);
        }

        prog.funcs.push(func);
        idx
    }

    fn new_extern(
        &mut self,
        map_name: Path,
        link_name: Path,
        ty: TyScheme,
        is_mutable: bool,
        modifiers: Vec<Modifier>,
        is_intrinsic: bool,
        intrinsic_kind: Option<lir::IntrinsicKind>,
        src: Option<String>,
    ) {
        let idx = self.prog.borrow().externs.len();
        let mut prog = self.prog.borrow_mut();
        prog.extern_map.insert(map_name, idx);
        prog.externs.push(lir::Extern {
            name: link_name,
            ty,
            is_mutable,
            modifiers,
            is_intrinsic,
            intrinsic_kind,
            src,
        });
    }

    fn is_extern(&self, name: &Path) -> bool {
        let prog = self.prog.borrow();
        prog.extern_map.contains_key(name)
    }

    fn extern_link_name(&self, name: &Path) -> Option<Path> {
        let prog = self.prog.borrow();
        let idx = prog.extern_map.get(name)?;
        Some(prog.externs[*idx].name.clone())
    }

    fn new_global(&mut self, name: &Path, init_value: lir::Value, ty: TyScheme, mutable: bool) {
        let mut prog = self.prog.borrow_mut();
        let path = prog.module_path.to_path();
        let idx = prog.globals.len();
        let name = name.to_string();
        self.global_idx.insert(name.clone(), idx);
        prog.globals.push(lir::Global {
            idx,
            path,
            name,
            ty,
            init_value,
            mutable,
        });
    }

    fn add_trait_member(&mut self, name: Path) {
        let mut prog = self.prog.borrow_mut();
        // we explicitly remove all non-name path parts
        prog.trait_member_set.insert(name.with_names_only());
    }

    fn data(&mut self, value: Vec<u8>) -> usize {
        if let Some(idx) = self.data_idx.get(&value) {
            return *idx;
        }

        let mut prog = self.prog.borrow_mut();
        let path = prog.module_path.to_path();
        let idx = prog.data.len();
        self.data_idx.insert(value.clone(), idx);

        prog.data.push(lir::Data::new(idx, path, value));
        idx
    }

    fn get_or_set_local(&mut self, value: lir::Value, ty: TyScheme) -> Option<usize> {
        if ty.is_unit() {
            if let Some(i) = value.to_inst() {
                self.push(i);
            }
            None
        } else if let Some(idx) = value.local() {
            if let Some(builder) = self.builder.as_ref() {
                log::debug!(
                    "reuse local {} existing_ty={} new_ty={}",
                    idx,
                    builder.locals[idx].ty,
                    ty
                );
            }
            Some(idx)
        } else {
            log::debug!("alloc new local ty={}", ty);
            let idx = self.local(ty.clone());
            self.set_local(idx, value);
            Some(idx)
        }
    }

    fn set_local(&mut self, idx: usize, value: lir::Value) {
        self.push(lir::Inst::SetLocal(idx.into(), value));
    }

    pub fn with_new_block<F, T>(&mut self, f: F) -> (usize, T)
    where
        F: FnOnce(&mut Self) -> T,
    {
        // to prevent nested blocks, don't create a new block if the current is empty
        let (label, prev_block) = if self.blocks.len() != 0 && self.block().is_empty() {
            (self.curr_block, self.curr_block)
        } else {
            let label = self.new_block();
            (label, self.curr_block)
        };

        self.curr_block = label;
        let t = f(self);
        self.curr_block = prev_block;
        (label, t)
    }

    pub fn with_block<F, T>(&mut self, label: usize, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let prev_block = self.curr_block;
        self.curr_block = label;
        let v = f(self);
        self.curr_block = prev_block;
        v
    }

    pub fn with_block_capture<F, T>(&mut self, label: usize, f: F) -> (T, usize)
    where
        F: FnOnce(&mut Self) -> T,
    {
        let prev_block = self.curr_block;
        self.curr_block = label;
        let v = f(self);
        let end_block = self.curr_block;
        self.curr_block = prev_block;
        (v, end_block)
    }

    pub fn with_entry_block<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let entry_label = if let Some(label) = self.entry_block {
            label
        } else {
            let label = self.new_block();
            self.entry_block = Some(label);
            label
        };

        let prev_block = self.curr_block;
        self.curr_block = entry_label;
        let result = f(self);
        self.curr_block = prev_block;
        result
    }

    pub fn with_exit_block<F>(&mut self, f: F)
    where
        F: FnOnce(&mut Self),
    {
        let exit_block = if let Some(label) = self.exit_block {
            label
        } else {
            let label = self.new_block();
            self.exit_block = Some(label);
            label
        };

        let prev_block = self.curr_block;
        self.curr_block = exit_block;
        f(self);
        self.curr_block = prev_block;
    }

    pub fn call_from_op(
        &mut self,
        operator_id: NodeId,
        args: &[&Node<Expr>],
    ) -> RayResult<GenResult> {
        let resolved = call_resolution(self.db, operator_id).unwrap_or_else(|| {
            let source = self.srcmap.get_by_id(operator_id);
            panic!(
                "missing call resolution for operator {:?} ({:?})",
                operator_id, source,
            )
        });

        let mut call_args: Vec<lir::Variable> = Vec::with_capacity(args.len());
        for arg in args {
            let arg_ty = self.ty_of(arg.id);
            let arg_val = arg.lir_gen(self)?;
            call_args.push(self.value_to_local_or_unit(arg_val, arg_ty));
        }

        let target = resolved.target().expect("call resolution missing target");
        let base_fqn = def_path(self.db, target.clone())
            .expect("missing def_path for call target")
            .to_path();

        let fn_name = if self.is_extern(&base_fqn) {
            self.extern_link_name(&base_fqn)
                .unwrap_or_else(|| base_fqn.clone())
        } else {
            mangle::fn_name(&base_fqn, &resolved.callee_ty)
        };

        self.add_sym(fn_name.clone());
        Ok(lir::Call::new(
            fn_name,
            call_args,
            resolved.callee_ty.clone(),
            Some(resolved.poly_callee_ty.clone()),
        )
        .into())
    }

    fn get_closure_info(&self, node_id: NodeId) -> Option<ClosureInfo> {
        closure_info(self.db, node_id)
    }

    /// Returns the LocalBindingId for a node using the query system.
    ///
    /// For pattern nodes (parameters, let-bindings), this looks up the pattern_records.
    /// For name expression nodes (references to locals), this looks up name_resolutions.
    fn binding_for_node(&self, node_id: NodeId) -> Option<LocalBindingId> {
        // First try pattern_records (for pattern definition sites)
        if let Some(binding) = local_binding_for_node(self.db, node_id) {
            return Some(binding);
        }
        // Fall back to name_resolutions (for name usage sites)
        let resolutions = name_resolutions(self.db, node_id.owner.file);
        if let Some(Resolution::Local(binding)) = resolutions.get(&node_id) {
            return Some(*binding);
        }
        None
    }

    /// Generate a fallback debug name for a binding when no AST name is available.
    fn fallback_binding_name(&self, binding: LocalBindingId) -> String {
        format!("__local_{}", binding.index)
    }

    /// Check if this binding refers to a global variable and return the variable if so.
    /// A binding is global if its owner is FileMain (def_id.index == 0).
    fn global_var_for_binding(
        &self,
        binding: LocalBindingId,
        path: &Path,
    ) -> Option<lir::Variable> {
        // Global bindings are owned by FileMain (index 0)
        if binding.owner.index != 0 {
            return None;
        }
        let global = self.global_idx.get(&path.to_string())?;
        Some(lir::Variable::Global(self.path(), *global))
    }

    fn ensure_local_for_binding(
        &mut self,
        binding: LocalBindingId,
        debug_name: String,
        ty: TyScheme,
    ) -> usize {
        self.get_var(&binding).copied().unwrap_or_else(|| {
            let idx = self.local(ty);
            self.set_var(binding, debug_name, idx);
            idx
        })
    }

    fn maybe_direct_function(&self, node_id: NodeId) -> Option<TyScheme> {
        let ty = ty_of(self.db, node_id)?;

        let scheme = TyScheme::from_mono(ty);
        if !matches!(scheme.mono(), Ty::Func(_, _)) {
            return None;
        }

        // Use existing name resolution for this node
        let resolutions = name_resolutions(self.db, node_id.owner.file);
        let Some(Resolution::Def(def_target)) = resolutions.get(&node_id) else {
            return None; // locals, type params, primitives
        };

        // Check if it's a function/method definition (works for both workspace and library defs)
        let record = definition_record(self.db, def_target.clone())?;
        if matches!(record.kind, DefKind::Function { .. } | DefKind::Method) {
            Some(scheme)
        } else {
            None
        }
    }

    fn collect_closure_captures(&mut self, closure_id: NodeId) -> Vec<lir::CaptureSlot> {
        let info = self
            .get_closure_info(closure_id)
            .expect("closure info missing for node");

        // ClosureInfo.captures is already Vec<LocalBindingId>
        info.captures
            .iter()
            .map(|binding| {
                // Get the type from the binding
                let ty = self.local_ty_of(*binding);
                let var = self
                    .get_var(binding)
                    .copied()
                    .map(lir::Variable::Local)
                    .unwrap_or_else(|| {
                        panic!(
                            "capture `{:?}` is not available in the current scope",
                            binding
                        )
                    });
                lir::CaptureSlot {
                    binding: *binding,
                    ty,
                    value: var,
                }
            })
            .collect()
    }

    fn ensure_fn_handle_type(&mut self, sig: &Ty) -> StructTy {
        let (params, ret) = match sig {
            Ty::Func(params, ret) => (params.clone(), *ret.clone()),
            _ => panic!("ensure_fn_handle_type: expected function type, got {}", sig),
        };

        let key = (params.clone(), ret.clone());
        if let Some(existing) = self.fn_handle_types.get(&key) {
            return existing.clone();
        }

        // Semantic signature: fn(A..)->R
        // ABI code pointer:   fn(rawptr[u8], A..)->R
        let mut abi_params = Vec::with_capacity(params.len() + 1);
        abi_params.push(Ty::rawptr(Ty::u8()));
        abi_params.extend(params.clone());

        let code_ty = Ty::Func(abi_params, Box::new(ret.clone()));

        let module_path = ModulePath::new(self.path().to_name_vec());
        let path = ItemPath::new(
            module_path,
            vec!["__fn_handle".into(), mangle::fn_ty(&params, &ret).into()],
        );

        let ty = TyScheme::from_mono(Ty::Const(path.clone()));

        let struct_ty = StructTy {
            kind: NominalKind::Struct,
            path: path.clone(),
            ty: ty.clone(),
            fields: vec![
                // Code pointer has ABI fn(rawptr[u8], A..)->R
                (str!("__fn"), TyScheme::from_mono(code_ty)),
                // Env pointer is opaque rawptr[u8]
                (str!("__env"), TyScheme::from_mono(Ty::rawptr(Ty::u8()))),
            ],
        };

        self.fn_handle_types.insert(key, struct_ty.clone());
        self.fn_handle_path_types.insert(path, struct_ty.clone());
        struct_ty
    }

    fn ensure_fn_wrapper_for_function(
        &mut self,
        name: &Path,
        fn_ty: &TyScheme,
    ) -> (Path, TyScheme) {
        let (params, ret) = match fn_ty.mono() {
            Ty::Func(params, ret) => (params.clone(), *ret.clone()),
            other => panic!(
                "ensure_fn_wrapper_for_function: expected fn type, got {}",
                other
            ),
        };

        let key = (name.clone(), params.clone(), ret.clone());
        if let Some(existing) = self.fn_handle_wrappers.get(&key) {
            let mut abi_params = Vec::with_capacity(params.len() + 1);
            abi_params.push(Ty::rawptr(Ty::u8()));
            abi_params.extend(params.clone());
            let wrapper_ty = TyScheme::from_mono(Ty::Func(abi_params, Box::new(ret.clone())));
            return (existing.clone(), wrapper_ty);
        }

        // Build a new wrapper: fn(rawptr[u8], A1, .., An) -> R { name(A1..An) }
        let mut wrapper_path = name.clone();
        wrapper_path = wrapper_path.append("$fn_handle");

        let outer_builder = self.with_builder(Builder::new());

        let wrapper_ty = {
            let mut abi_params = Vec::with_capacity(params.len() + 1);
            abi_params.push(Ty::rawptr(Ty::u8()));
            abi_params.extend(params.clone());
            TyScheme::from_mono(Ty::Func(abi_params, Box::new(ret.clone())))
        };

        self.with_entry_block(|ctx| {
            // env param, ignored
            let _env_loc = ctx.param_unbound("__env".to_string(), Ty::rawptr(Ty::u8()).into());

            // value params
            let mut arg_vars = Vec::with_capacity(params.len());
            for (i, param_ty) in params.iter().enumerate() {
                let name = format!("__arg{}", i);
                let loc = ctx.param_unbound(
                    name.clone(),
                    TyScheme::from_mono(param_ty.clone()).into_mono(),
                );
                arg_vars.push(lir::Variable::Local(loc));
            }

            // Call original function
            ctx.add_sym(name.clone());
            let call = lir::Call::new(name.clone(), arg_vars, fn_ty.clone(), None);

            if ret.is_unit() {
                ctx.push(call.into());
                ctx.ret(lir::Value::Empty);
            } else {
                // store call result in temp then return it
                let tmp_loc = ctx.local(TyScheme::from_mono(ret.clone()));
                ctx.set_local(tmp_loc, call.into());
                ctx.ret(lir::Variable::Local(tmp_loc).into());
            }
        });

        let builder = self.builder.take().unwrap();
        let (params_ir, locals, blocks, symbols, cfg) = builder.done();

        let mut func = lir::Func::new(
            wrapper_path.clone(),
            wrapper_ty.clone(),
            vec![],
            symbols,
            cfg,
            None, // synthetic wrapper function
        );
        func.params = params_ir;
        func.locals = locals;
        func.blocks = blocks;

        self.new_func(func);

        if let Some(prev) = outer_builder {
            self.builder = Some(prev);
        }

        self.fn_handle_wrappers.insert(key, wrapper_path.clone());
        (wrapper_path, wrapper_ty)
    }

    fn ensure_closure_env_type(
        &mut self,
        closure_id: NodeId,
        captures: &[lir::CaptureSlot],
    ) -> StructTy {
        if let Some(existing) = self.closure_env_types.get(&closure_id) {
            return existing.clone();
        }

        let module_path = ModulePath::new(self.path().to_name_vec());
        let path = ItemPath::new(
            module_path,
            vec![format!("__closure_env_{:x}", closure_id).into()],
        );

        let fields = captures
            .iter()
            .map(|slot| (slot.id(), slot.ty.clone()))
            .collect();

        let ty = TyScheme::from_mono(Ty::Const(path.clone()));
        let struct_ty = StructTy {
            kind: NominalKind::Struct,
            path: path.clone(),
            ty,
            fields,
        };

        self.closure_env_types.insert(closure_id, struct_ty.clone());
        struct_ty
    }

    fn ensure_closure_value_type(&mut self, closure_id: NodeId, fn_ty: &TyScheme) -> StructTy {
        if let Some(existing) = self.closure_value_types.get(&closure_id) {
            return existing.clone();
        }

        let sig = match fn_ty.mono() {
            Ty::Func(params, ret) if !params.is_empty() => {
                // params[0] is Env*, params[1..] are the semantic args
                Ty::Func(params[1..].to_vec(), ret.clone())
            }
            other => panic!("closure fn type is not (Env, ...)->R: {}", other),
        };
        self.ensure_fn_handle_type(&sig)
    }

    fn make_closure_path(&self, info: &ClosureInfo, expr_id: NodeId) -> Path {
        // Use def_path query to get the parent definition's path
        if let Some(parent_path) = def_path(self.db, DefTarget::Workspace(info.parent_def)) {
            return parent_path
                .to_path()
                .append(format!("$closure_{:x}", expr_id));
        }

        // Fallback: use module path
        self.path().append(format!("$closure_{:x}", expr_id))
    }

    fn lower_closure(
        &mut self,
        expr: &Node<Expr>,
        closure: &Closure,
        captures: &[lir::CaptureSlot],
        env_ty: &StructTy,
    ) -> RayResult<Path> {
        if let Some(existing) = self.closure_funcs.get(&expr.id) {
            return Ok(existing.clone());
        }

        let outer_builder = self.with_builder(Builder::new());

        self.with_entry_block(|ctx| {
            // ABI env parameter: rawptr[u8]
            let env_param_ty = TyScheme::from_mono(Ty::rawptr(Ty::u8())).into_mono();
            let env_raw_loc = ctx.param_unbound("__env".to_string(), env_param_ty.clone());
            let env_raw_var = lir::Variable::Local(env_raw_loc);

            // closure arguments
            for param in closure.args.items.iter() {
                if let Expr::Name(name) = &param.value {
                    let binding = ctx.binding_for_node(param.id).unwrap_or_else(|| {
                        panic!("missing binding for closure param {:#x}", param.id)
                    });
                    let param_name = name
                        .path
                        .name()
                        .unwrap_or_else(|| ctx.fallback_binding_name(binding));
                    let ty = ctx.ty_of(param.id);
                    ctx.param(binding, param_name, ty.clone().into_mono());
                } else {
                    todo!("non-name closure parameters are not supported yet");
                }
            }

            // Cast rawptr[u8] to rawptr[Env] where Env is the concrete env struct type
            let env_struct_scheme = env_ty.ty.clone();
            let env_cast = lir::Cast::new(
                env_raw_var.clone(),
                Ty::rawptr(env_struct_scheme.mono().clone()),
            );
            let env_struct_loc = ctx
                .get_or_set_local(env_cast.into(), env_struct_scheme.clone())
                .expect("env cast should create a local");
            let env_struct_var = lir::Variable::Local(env_struct_loc);

            for slot in captures {
                let value = lir::GetField {
                    src: env_struct_var.clone(),
                    field: slot.id(),
                }
                .into();
                let capture_loc = ctx.local(slot.ty.clone());
                ctx.set_local(capture_loc, value);
                ctx.set_var(slot.binding, slot.id(), capture_loc);
            }
        });

        let body = closure.body.as_ref();
        let body_val = if !matches!(body.value, Expr::Block(_)) {
            let (_, value) = self.with_new_block(|ctx| body.lir_gen(ctx));
            value?
        } else {
            body.lir_gen(self)?
        };

        // Use raw_ty_of to get the actual function type, not the fn_handle wrapper
        let mut fn_ty_with_env = self.raw_ty_of(expr.id);
        match fn_ty_with_env.mono_mut() {
            Ty::Func(params, _) => {
                let mut new_params = Vec::with_capacity(params.len() + 1);
                new_params.push(Ty::rawptr(Ty::u8())); // ABI env parameter
                new_params.extend(params.iter().cloned());
                *params = new_params;
            }
            other => panic!("closure type is not a function: {}", other),
        }

        self.closure_fn_types
            .insert(expr.id, fn_ty_with_env.clone());

        self.with_exit_block(|ctx| {
            let (_, _, _, ret_ty) = fn_ty_with_env
                .try_borrow_fn()
                .expect("closure function type");
            let value = if !ret_ty.is_unit() {
                let body_ty = ctx.ty_of(body.id);
                let body_loc = ctx.get_or_set_local(body_val, body_ty).unwrap();
                lir::Variable::Local(body_loc).into()
            } else {
                if let Some(i) = body_val.to_inst() {
                    ctx.push(i);
                }
                lir::Value::Empty
            };

            ctx.ret(value);
        });

        let builder = self.builder.take().unwrap();
        let (params, locals, blocks, symbols, cfg) = builder.done();

        let info = self
            .get_closure_info(expr.id)
            .expect("closure info missing for node");
        let fn_path = self.make_closure_path(&info, expr.id);
        let mut func = lir::Func::new(
            fn_path.clone(),
            fn_ty_with_env.clone(),
            Vec::new(),
            symbols,
            cfg,
            Some(expr.id),
        );
        func.params = params;
        func.locals = locals;
        func.blocks = blocks;
        self.new_func(func);

        self.closure_funcs.insert(expr.id, fn_path.clone());

        if let Some(prev_builder) = outer_builder {
            self.builder = Some(prev_builder);
        }

        Ok(fn_path)
    }

    fn build_closure_env(
        &mut self,
        captures: &[lir::CaptureSlot],
        env_ty: &StructTy,
    ) -> RayResult<lir::Variable> {
        let env_loc = self.local(env_ty.ty.clone());
        self.push(lir::Inst::StructInit(
            lir::Variable::Local(env_loc),
            env_ty.clone(),
        ));

        for slot in captures {
            let value: lir::Value = slot.value.clone().into();
            self.push(lir::SetField::new(
                lir::Variable::Local(env_loc),
                slot.id(),
                value,
            ));
        }

        Ok(lir::Variable::Local(env_loc))
    }

    fn build_closure_value(
        &mut self,
        handle_ty: &StructTy,
        fn_name: Path,
        fn_ty: TyScheme,
        env: lir::Variable,
        env_ty: &StructTy,
        poly_ty: Option<TyScheme>,
    ) -> RayResult<lir::Variable> {
        let handle_loc = self.local(handle_ty.ty.clone());
        self.push(lir::Inst::StructInit(
            lir::Variable::Local(handle_loc),
            handle_ty.clone(),
        ));

        let mut fn_ref = lir::FuncRef::new(fn_name.clone(), fn_ty.clone());
        fn_ref.poly_ty = poly_ty;
        self.add_sym(fn_name.clone());
        self.push(lir::SetField::new(
            lir::Variable::Local(handle_loc),
            str!("__fn"),
            lir::Atom::FuncRef(fn_ref).into(),
        ));

        let rawptr_ty = Ty::rawptr(Ty::u8());
        let env_addr = lir::Lea::new(env, lir::LeaOffset::zero());
        let env_addr_loc = self
            .get_or_set_local(
                env_addr,
                TyScheme::from_mono(Ty::rawptr(env_ty.ty.mono().clone())),
            )
            .expect("env lea should create a local");
        let env_cast = lir::Cast::new(lir::Variable::Local(env_addr_loc), rawptr_ty.clone());
        let env_loc = self
            .get_or_set_local(env_cast, TyScheme::from_mono(rawptr_ty))
            .expect("env cast should create a local");
        self.push(lir::SetField::new(
            lir::Variable::Local(handle_loc),
            str!("__env"),
            lir::Variable::Local(env_loc).into(),
        ));

        Ok(lir::Variable::Local(handle_loc))
    }

    fn build_fn_handle_for_function(&mut self, name: Path, fn_ty: TyScheme) -> lir::Variable {
        // semantic sig fn(A..)->R
        let sig = fn_ty.mono().clone();
        let handle_struct = self.ensure_fn_handle_type(&sig);

        // ABI wrapper fn(rawptr[u8], A..)->R
        let (wrapper_name, wrapper_ty) = self.ensure_fn_wrapper_for_function(&name, &fn_ty);

        let handle_loc = self.local(handle_struct.ty.clone());
        self.push(lir::Inst::StructInit(
            lir::Variable::Local(handle_loc),
            handle_struct.clone(),
        ));

        let fn_ref = lir::FuncRef::new(wrapper_name.clone(), wrapper_ty.clone());
        self.add_sym(wrapper_name);

        self.push(lir::SetField::new(
            lir::Variable::Local(handle_loc),
            str!("__fn"),
            lir::Atom::FuncRef(fn_ref).into(),
        ));

        // __env = null
        self.push(lir::SetField::new(
            lir::Variable::Local(handle_loc),
            str!("__env"),
            lir::Atom::uptr(0).into(),
        ));

        lir::Variable::Local(handle_loc)
    }

    fn emit_fnhandle_call(
        &mut self,
        callee_id: NodeId,
        callee_val: lir::Value,
        call_args: Vec<lir::Variable>,
        original_poly_ty: Option<TyScheme>,
        src: &Source,
    ) -> RayResult<GenResult> {
        // callee_val has type FnHandle[A..,R]
        let handle_scheme = self.ty_of(callee_id);
        let handle_loc = self
            .get_or_set_local(callee_val, handle_scheme.clone())
            .unwrap();
        let handle_var = lir::Variable::Local(handle_loc);

        // Extract env and code pointer from the handle.
        let handle_struct_ty = match handle_scheme.mono() {
            Ty::Const(fqn) => self.fn_handle_path_types.get(fqn).cloned().expect(&format!(
                "could not find function handle struct type: {}",
                fqn
            )),
            other => panic!("callee is not a FnHandle: {}", other),
        };

        // Get __env: rawptr[u8]
        let (_, env_ty_scheme) = handle_struct_ty
            .get_field("__env")
            .expect("FnHandle missing __env field");
        let env_val = lir::GetField {
            src: handle_var.clone(),
            field: str!("__env"),
        }
        .into();
        let env_loc = self
            .get_or_set_local(env_val, env_ty_scheme.clone())
            .expect("env field should produce local");

        // Get __fn: code pointer; its type is (Env*, A..)->R or (A..)->R for plain fns.
        let (_, fn_field_ty_scheme) = handle_struct_ty
            .get_field("__fn")
            .expect("FnHandle missing __fn field");
        let fn_val = lir::GetField {
            src: handle_var.clone(),
            field: str!("__fn"),
        }
        .into();
        let fn_loc = self
            .get_or_set_local(fn_val, fn_field_ty_scheme.clone())
            .expect("fn field should produce local");

        // Prepend env arg.
        let mut args_with_env = Vec::with_capacity(call_args.len() + 1);
        args_with_env.push(lir::Variable::Local(env_loc));
        args_with_env.extend(call_args);

        let mut direct = lir::Call::new_ref(
            fn_loc,
            args_with_env,
            fn_field_ty_scheme.clone(),
            original_poly_ty,
        );
        direct.source = Some(src.clone());
        Ok(direct.into())
    }

    fn emit_resolved_direct_call(
        &mut self,
        resolved: &CallResolution,
        call_args: Vec<lir::Variable>,
        src: &Source,
    ) -> RayResult<GenResult> {
        let target = resolved.target().expect("call resolution missing target");
        let base_fqn = def_path(self.db, target.clone())
            .expect("missing def_path for call target")
            .to_path();

        let fn_name = if self.is_extern(&base_fqn) {
            self.extern_link_name(&base_fqn)
                .unwrap_or_else(|| base_fqn.clone())
        } else {
            mangle::fn_name(&base_fqn, &resolved.callee_ty)
        };

        log::debug!("add sym: {}", fn_name);
        self.add_sym(fn_name.clone());
        let mut call = lir::Call::new(
            fn_name,
            call_args,
            resolved.callee_ty.clone(),
            Some(resolved.poly_callee_ty.clone()),
        );
        call.source = Some(src.clone());
        Ok(call.into())
    }

    fn resolve_trait_method_direct_call(
        &self,
        trait_fqn: &ItemPath,
        method_name: &str,
        callee_ty: TyScheme,
    ) -> Option<CallResolution> {
        let trait_target = def_for_path(self.db, trait_fqn.clone())?;
        let trait_definition = trait_def(self.db, trait_target.clone())?;
        let method_info = trait_definition.find_method(method_name)?;

        let poly_callee_ty = method_info.scheme.clone();
        let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
            Ok((_, subst)) => subst,
            Err(_) => Subst::new(),
        };

        Some(CallResolution {
            trait_target: Some(method_info.target.clone()),
            impl_target: None,
            poly_callee_ty,
            callee_ty,
            subst,
        })
    }

    fn emit_trait_method_call_with_recv_local(
        &mut self,
        trait_fqn: &ItemPath,
        method_name: &str,
        recv_loc: usize,
        recv_scheme: TyScheme,
        callee_ty: TyScheme,
        src: &Source,
    ) -> RayResult<Option<usize>> {
        let resolved = self
            .resolve_trait_method_direct_call(trait_fqn, method_name, callee_ty)
            .unwrap_or_else(|| {
                panic!(
                    "could not resolve trait method `{}` on `{}`",
                    method_name, trait_fqn
                )
            });

        let recv_param_mono = match resolved.callee_ty.mono() {
            Ty::Func(params, _) => params.first(),
            _ => None,
        };
        let target = resolved.target().expect("call resolution missing target");
        let recv_mode = self.recv_mode_for_base(target);

        let recv_val: lir::Value = lir::Variable::Local(recv_loc).into();
        let recv_var = if let Some(param_mono) = recv_param_mono {
            self.maybe_coerce_receiver_arg(recv_val.clone(), &recv_scheme, param_mono, recv_mode)
                .unwrap_or_else(|| self.value_to_local_or_unit(recv_val, recv_scheme.clone()))
        } else {
            self.value_to_local_or_unit(recv_val, recv_scheme.clone())
        };

        let call_val = self.emit_resolved_direct_call(&resolved, vec![recv_var], src)?;
        let ret_scheme = match resolved.callee_ty.mono() {
            Ty::Func(_, ret) => TyScheme::from_mono((**ret).clone()),
            _ => TyScheme::from_mono(Ty::unit()),
        };
        Ok(self.get_or_set_local(call_val, ret_scheme))
    }

    fn emit_pattern_bind_or_guard(
        &mut self,
        pat: &Node<Pattern>,
        pat_scheme: &TyScheme,
        elem_val: lir::Value,
        cond_label: usize,
        body: &Node<Expr>,
    ) -> RayResult<bool> {
        match &pat.value {
            Pattern::Missing(_) => Ok(false),
            Pattern::Name(name) => {
                let binding = self.binding_for_node(pat.id).unwrap_or_else(|| {
                    panic!(
                        "missing binding for `for` pattern {:#x} ({})",
                        pat.id, name.path
                    )
                });
                let debug_name = name
                    .path
                    .name()
                    .unwrap_or_else(|| self.fallback_binding_name(binding));
                let slot = self.ensure_local_for_binding(binding, debug_name, pat_scheme.clone());
                self.set_local(slot, elem_val);
                Ok(false)
            }
            Pattern::Some(inner_pat) => {
                let elem_loc = self.local(pat_scheme.clone());
                self.set_local(elem_loc, elem_val);

                let elem_mono = pat_scheme.mono().clone();
                let elem_is_some_val = lir::GetField {
                    src: lir::Variable::Local(elem_loc),
                    field: str!("is_some"),
                }
                .into();
                let elem_is_some_loc = self
                    .get_or_set_local(elem_is_some_val, Ty::bool().into())
                    .unwrap();

                let match_label = self.new_block();
                self.cond(elem_is_some_loc, match_label, cond_label);

                self.with_block(match_label, |ctx| -> RayResult<()> {
                    let payload_mono = elem_mono.nilable_payload().cloned().unwrap_or(Ty::Never);
                    let inner_val = lir::GetField {
                        src: lir::Variable::Local(elem_loc),
                        field: str!("payload"),
                    }
                    .into();

                    match &inner_pat.value {
                        Pattern::Name(name) => {
                            let binding = ctx.binding_for_node(inner_pat.id).unwrap_or_else(|| {
                                panic!(
                                    "missing binding for `for` pattern {:#x} ({})",
                                    inner_pat.id, name.path
                                )
                            });
                            let debug_name = name
                                .path
                                .name()
                                .unwrap_or_else(|| ctx.fallback_binding_name(binding));
                            let slot = ctx.ensure_local_for_binding(
                                binding,
                                debug_name,
                                TyScheme::from_mono(payload_mono),
                            );
                            ctx.set_local(slot, inner_val);
                        }
                        _ => todo!("lir_gen: Expr::For: complex `some(...)` pattern"),
                    }

                    let body_val = body.lir_gen(ctx)?;
                    if let Some(i) = body_val.to_inst() {
                        ctx.push(i);
                    }
                    ctx.goto(cond_label);
                    Ok(())
                })?;

                Ok(true)
            }
            _ => todo!("lir_gen: Expr::For: pattern {}", pat.value),
        }
    }

    fn select_iterable_iterator_ty(
        &self,
        iterable_trait_fqn: &ItemPath,
        container_ty: &Ty,
        elem_ty: &Ty,
    ) -> Option<Ty> {
        // Get the trait's DefTarget
        let trait_target = def_for_path(self.db, iterable_trait_fqn.clone())?;

        // Get all impls for this trait
        let impl_targets = impls_for_trait(self.db, trait_target);

        for impl_target in impl_targets.iter() {
            let impl_def = impl_def(self.db, impl_target.clone());
            let Some(impl_def) = impl_def.deref() else {
                continue;
            };
            let impl_ty = impl_def.convert_to_impl_ty();

            let ImplKind::Trait { trait_ty, .. } = &impl_ty.kind else {
                continue;
            };

            let Ty::Proj(trait_path, args) = trait_ty else {
                continue;
            };
            if trait_path != iterable_trait_fqn {
                continue;
            }

            let (impl_container_ty, impl_iter_ty, impl_elem_ty) = match &args[..] {
                [c, i, e] => (c, i, e),
                _ => continue,
            };

            let mut poly_vars = HashSet::new();
            for v in impl_container_ty
                .free_vars()
                .into_iter()
                .chain(impl_iter_ty.free_vars())
                .chain(impl_elem_ty.free_vars())
            {
                poly_vars.insert(v.clone());
            }

            let mut subst = Subst::new();
            if !match_ty(impl_container_ty, container_ty, &poly_vars, &mut subst) {
                continue;
            }
            if !match_ty(impl_elem_ty, elem_ty, &poly_vars, &mut subst) {
                continue;
            }

            let mut iter_ty = impl_iter_ty.clone();
            iter_ty.apply_subst(&subst);
            return Some(iter_ty);
        }

        None
    }

    fn emit_named_direct_call(
        &mut self,
        fn_name: Path,
        call_args: Vec<lir::Variable>,
        fn_ty: TyScheme,
        original_poly_ty: Option<TyScheme>,
        src: &Source,
    ) -> RayResult<GenResult> {
        log::debug!("add sym: {}", fn_name);
        self.add_sym(fn_name.clone());
        let mut call = lir::Call::new(fn_name, call_args, fn_ty, original_poly_ty);
        call.source = Some(src.clone());
        Ok(call.into())
    }

    /// Emit a string literal value and return its local index.
    fn emit_string_literal(&mut self, s: &str) -> usize {
        let bytes = s.as_bytes().to_vec();
        let len = bytes.len();
        let char_len = s.chars().count();
        let string_size = lir::Size::bytes(len);
        let idx = self.data(bytes);

        let data_loc = self.local(Ty::ref_of(Ty::u8()).into());
        let ptr = lir::Malloc::new(Ty::u8().into(), lir::Atom::uptr(len as u64));
        self.set_local(data_loc, ptr.into());

        let path = self.path();
        self.push(lir::Inst::MemCopy(
            lir::Variable::Local(data_loc),
            lir::Variable::Data(path, idx),
            string_size.into(),
        ));

        let string_target = resolve_builtin(self.db, self.file_id, "string".to_string())
            .expect("string type not in scope");
        let string_fqn = def_path(self.db, string_target).expect("missing def_path for string");
        let string_ty = Ty::Const(string_fqn.clone());
        let loc = self.local(string_ty.clone().into());
        self.push(lir::Inst::StructInit(
            lir::Variable::Local(loc),
            StructTy {
                kind: NominalKind::Struct,
                path: string_fqn,
                ty: string_ty.into(),
                fields: vec![
                    (str!("raw_ptr"), Ty::ref_of(Ty::u8()).into()),
                    (str!("len"), Ty::uint().into()),
                    (str!("char_len"), Ty::uint().into()),
                ],
            },
        ));

        self.push(lir::SetField::new(
            lir::Variable::Local(loc),
            str!("raw_ptr"),
            lir::Variable::Local(data_loc).into(),
        ));

        self.push(lir::SetField::new(
            lir::Variable::Local(loc),
            str!("len"),
            lir::Atom::Size(string_size).into(),
        ));

        self.push(lir::SetField::new(
            lir::Variable::Local(loc),
            str!("char_len"),
            lir::Atom::uptr(char_len as u64).into(),
        ));

        loc
    }

    fn maybe_coerce_receiver_arg(
        &mut self,
        value: lir::Value,
        expr_ty_scheme: &TyScheme,
        param_mono: &Ty,
        recv_mode: ReceiverMode,
    ) -> Option<lir::Variable> {
        let expr_mono = expr_ty_scheme.mono().clone();

        match recv_mode {
            ReceiverMode::Ptr => {
                if let Ty::Ref(inner) = param_mono {
                    if **inner == expr_mono {
                        let val_loc = self
                            .get_or_set_local(value, expr_ty_scheme.clone())
                            .unwrap();

                        let lea =
                            lir::Lea::new(lir::Variable::Local(val_loc), lir::LeaOffset::zero());

                        let ptr_scheme = TyScheme::from_mono(param_mono.clone());
                        let var =
                            if let Some(ptr_loc) = self.get_or_set_local(lea.into(), ptr_scheme) {
                                lir::Variable::Local(ptr_loc)
                            } else {
                                lir::Variable::Unit
                            };

                        return Some(var);
                    }
                }
            }
            ReceiverMode::Value => {
                if !matches!(param_mono, Ty::Ref(_))
                    && matches!(expr_mono, Ty::Ref(inner) if *inner == *param_mono)
                {
                    let val_loc = self
                        .get_or_set_local(value, expr_ty_scheme.clone())
                        .unwrap();
                    let load = lir::Load::new(lir::Variable::Local(val_loc), lir::Size::zero());
                    let val_scheme = TyScheme::from_mono(param_mono.clone());
                    let loaded_loc = self.get_or_set_local(load.into(), val_scheme).unwrap();
                    return Some(lir::Variable::Local(loaded_loc));
                }
            }
            ReceiverMode::None => {}
        }

        None
    }

    fn value_to_local_or_unit(&mut self, value: lir::Value, ty: TyScheme) -> lir::Variable {
        if let Some(loc) = self.get_or_set_local(value, ty) {
            lir::Variable::Local(loc)
        } else {
            lir::Variable::Unit
        }
    }

    fn recv_mode_for_base(&self, target: &DefTarget) -> ReceiverMode {
        method_receiver_mode(self.db, target.clone())
    }

    fn build_call_args(
        &mut self,
        is_method_call: bool,
        recv_mode: ReceiverMode,
        arg_exprs: Vec<(&Node<Expr>, TyScheme)>,
        param_monos: &[Ty],
    ) -> RayResult<Vec<lir::Variable>> {
        let mut call_args: Vec<lir::Variable> = Vec::new();

        for (idx, (expr, expr_ty_scheme)) in arg_exprs.into_iter().enumerate() {
            log::debug!(
                "call arg[{}] id={:#x} ty = {} expr = {:?}",
                idx,
                expr.id,
                self.ty_of(expr.id),
                expr
            );

            let value = expr.lir_gen(self)?;

            // Auto address-of for receiver arguments:
            // If this is a method call (e.m(...)) and the first
            // parameter type is *T while the receiver expression has
            // type T, take the address of the receiver value and pass
            // a pointer.
            if is_method_call && idx == 0 {
                if let Some(param_mono) = param_monos.get(0) {
                    let expr_mono = expr_ty_scheme.mono().clone();
                    log::debug!(
                        "[Call::lir_gen] expr_mono={}, param_mono={}, recv_mode={:?}",
                        expr_mono,
                        param_mono,
                        recv_mode
                    );

                    if let Some(var) = self.maybe_coerce_receiver_arg(
                        value.clone(),
                        &expr_ty_scheme,
                        param_mono,
                        recv_mode,
                    ) {
                        call_args.push(var);
                        continue;
                    }
                }
            }

            // Default case: treat the argument as having the callee's
            // parameter type when available; otherwise, fall back to
            // the expression's own type.
            let ty_for_local = if let Some(param_mono) = param_monos.get(idx) {
                TyScheme::from_mono(param_mono.clone())
            } else {
                self.ty_of(expr.id)
            };

            call_args.push(self.value_to_local_or_unit(value, ty_for_local));
        }

        Ok(call_args)
    }

    fn place_local_from_pattern(&mut self, pat: &Node<Pattern>) -> usize {
        match &pat.value {
            Pattern::Name(_) => {
                let binding = self
                    .binding_for_node(pat.id)
                    .unwrap_or_else(|| panic!("missing binding for place pattern {:#x}", pat.id));
                self.get_var(&binding)
                    .copied()
                    .unwrap_or_else(|| panic!("missing local for place binding {}", binding))
            }
            Pattern::Deref(Node { id, .. }) => {
                let binding = self.binding_for_node(*id).unwrap_or_else(|| {
                    panic!(
                        "missing binding for place pattern {:#x} (deref name {:#x})",
                        pat.id, id
                    )
                });
                self.get_var(&binding)
                    .copied()
                    .unwrap_or_else(|| panic!("missing local for place binding {}", binding))
            }
            _ => todo!("lir_gen: place_local_from_pattern for complex pattern"),
        }
    }

    fn emit_field_assign(
        &mut self,
        base_pat: &Node<Pattern>,
        field_name: &ast::Name,
        rhs_loc: Option<usize>,
    ) -> RayResult<()> {
        if let Some(rhs_loc) = rhs_loc {
            let base_loc = self.place_local_from_pattern(base_pat);
            self.push(lir::SetField::new(
                lir::Variable::Local(base_loc),
                field_name.path.name().unwrap(),
                lir::Variable::Local(rhs_loc).into(),
            ));
        }
        Ok(())
    }

    fn emit_index_assign(
        &mut self,
        assign_id: NodeId,
        container_pat: &Node<Pattern>,
        index_expr: &Node<Expr>,
        rhs_val: lir::Value,
        rhs_ty: TyScheme,
        src: &Source,
    ) -> RayResult<()> {
        let resolved = call_resolution(self.db, assign_id)
            .unwrap_or_else(|| panic!("missing call resolution for index assign {:#x}", assign_id));

        let param_monos = match resolved.callee_ty.mono() {
            Ty::Func(params, _) => params.clone(),
            _ => Vec::new(),
        };

        let target = resolved.target().expect("call resolution missing target");
        let recv_mode = self.recv_mode_for_base(target);

        let recv_param_mono = param_monos.first();

        // Evaluate the receiver as its actual value first (e.g. `list[T]`),
        // then coerce to the receiver param (e.g. `*list[T]`) if needed.
        // If we evaluate it as the param type up-front we can accidentally
        // skip emitting `lea` and end up mutating a copy (observed in `Index::set`).
        let recv_expr_scheme = self.ty_of(container_pat.id);
        let recv_value = self.emit_pattern_value(container_pat, &recv_expr_scheme, src)?;

        let recv_var = if let Some(param_mono) = recv_param_mono {
            self.maybe_coerce_receiver_arg(
                recv_value.clone(),
                &recv_expr_scheme,
                param_mono,
                recv_mode,
            )
            .unwrap_or_else(|| self.value_to_local_or_unit(recv_value, recv_expr_scheme.clone()))
        } else {
            self.value_to_local_or_unit(recv_value, recv_expr_scheme.clone())
        };

        let index_ty = self.ty_of(index_expr.id);
        let index_val = index_expr.lir_gen(self)?;
        let index_arg_ty = param_monos
            .get(1)
            .map(|ty| TyScheme::from_mono(ty.clone()))
            .unwrap_or(index_ty);
        let index_var = self.value_to_local_or_unit(index_val, index_arg_ty);

        let el_arg_ty = param_monos
            .get(2)
            .map(|ty| TyScheme::from_mono(ty.clone()))
            .unwrap_or(rhs_ty);
        let el_loc = self
            .get_or_set_local(rhs_val, el_arg_ty)
            .unwrap_or_default();
        let el_var = lir::Variable::Local(el_loc);

        let call_args = vec![recv_var, index_var, el_var];
        let call_val = self.emit_resolved_direct_call(&resolved, call_args, src)?;
        if let Some(i) = call_val.to_inst() {
            self.push(i);
        }

        Ok(())
    }

    fn emit_pattern_value(
        &mut self,
        pat: &Node<Pattern>,
        expected_ty: &TyScheme,
        src: &Source,
    ) -> RayResult<lir::Value> {
        match &pat.value {
            Pattern::Name(name) => {
                let binding = self.binding_for_node(pat.id).unwrap_or_else(|| {
                    panic!("missing binding for pattern {:#x} ({})", pat.id, pat)
                });
                let debug_name = name
                    .path
                    .name()
                    .unwrap_or_else(|| self.fallback_binding_name(binding));
                let idx = self.ensure_local_for_binding(binding, debug_name, expected_ty.clone());
                Ok(lir::Value::new(lir::Variable::Local(idx)))
            }
            Pattern::Deref(Node { id, value: name }) => {
                let binding = self.binding_for_node(*id).unwrap_or_else(|| {
                    panic!("missing binding for pattern {:#x} ({})", pat.id, pat)
                });
                let debug_name = name
                    .path
                    .name()
                    .unwrap_or_else(|| self.fallback_binding_name(binding));
                let idx = self.ensure_local_for_binding(binding, debug_name, expected_ty.clone());
                Ok(lir::Value::new(lir::Variable::Local(idx)))
            }
            Pattern::Dot(lhs, rhs) => {
                let lhs_ty = self.ty_of(lhs.id);
                let lhs_val = self.emit_pattern_value(lhs.as_ref(), &lhs_ty, src)?;
                let lhs_loc = self.get_or_set_local(lhs_val, lhs_ty.clone()).unwrap();

                Ok(lir::GetField {
                    src: lir::Variable::Local(lhs_loc),
                    field: rhs.path.name().unwrap(),
                }
                .into())
            }
            Pattern::Index(container_pat, index_expr, _) => {
                let resolved = call_resolution(self.db, pat.id).unwrap_or_else(|| {
                    panic!("missing call resolution for index pattern {:#x}", pat.id)
                });

                let param_monos = match resolved.callee_ty.mono() {
                    Ty::Func(params, _) => params.clone(),
                    _ => Vec::new(),
                };

                let target = resolved.target().expect("call resolution missing target");
                let recv_mode = self.recv_mode_for_base(target);
                let recv_param_mono = param_monos.first().cloned();
                let recv_expr_scheme = self.ty_of(container_pat.id);
                let recv_value =
                    self.emit_pattern_value(container_pat.as_ref(), &recv_expr_scheme, src)?;
                let recv_var = if let Some(param_mono) = recv_param_mono.as_ref() {
                    self.maybe_coerce_receiver_arg(
                        recv_value.clone(),
                        &recv_expr_scheme,
                        param_mono,
                        recv_mode,
                    )
                    .unwrap_or_else(|| {
                        self.value_to_local_or_unit(recv_value, recv_expr_scheme.clone())
                    })
                } else {
                    self.value_to_local_or_unit(recv_value, recv_expr_scheme.clone())
                };

                let index_ty = self.ty_of(index_expr.id);
                let index_val = index_expr.lir_gen(self)?;
                let index_arg_ty = param_monos
                    .get(1)
                    .map(|ty| TyScheme::from_mono(ty.clone()))
                    .unwrap_or(index_ty);
                let index_var = self.value_to_local_or_unit(index_val, index_arg_ty);

                let call_args = vec![recv_var, index_var];
                self.emit_resolved_direct_call(&resolved, call_args, src)
            }
            Pattern::Missing(_) => todo!("emit_pattern_value: Pattern::Missing"),
            Pattern::Sequence(_) => todo!("emit_pattern_value: Pattern::Sequence"),
            Pattern::Some(_) => todo!("emit_pattern_value: Pattern::Some"),
            Pattern::Tuple(_) => todo!("emit_pattern_value: Pattern::Tuple"),
        }
    }

    fn emit_assign_expr(
        &mut self,
        operator_id: NodeId,
        assign: &Assign,
        src: &Source,
    ) -> RayResult<lir::Value> {
        // Look up the type and generate RHS first
        let rhs_ty = self.ty_of(assign.rhs.id);
        let rhs_val = assign.rhs.lir_gen(self)?;
        let maybe_rhs_loc = self.get_or_set_local(rhs_val.clone(), rhs_ty.clone());

        self.emit_assign_to_pattern(
            operator_id,
            &assign.lhs,
            rhs_val,
            rhs_ty,
            maybe_rhs_loc,
            src,
        )?;

        Ok(lir::Value::Empty)
    }

    fn emit_assign_to_pattern(
        &mut self,
        assign_id: NodeId,
        lhs_pat: &Node<Pattern>,
        rhs_val: lir::Value,
        rhs_ty: TyScheme,
        rhs_loc: Option<usize>,
        src: &Source,
    ) -> RayResult<()> {
        match &lhs_pat.value {
            Pattern::Name(name) => {
                let Some(rhs_loc) = rhs_loc else {
                    log::debug!("  SKIP assign: rhs is unit");
                    return Ok(());
                };

                let lhs_ty = self.ty_of(lhs_pat.id);
                let binding = self.binding_for_node(lhs_pat.id).unwrap_or_else(|| {
                    panic!(
                        "missing binding for pattern {:#x} ({})",
                        lhs_pat.id, lhs_pat
                    )
                });
                let debug_name = name
                    .path
                    .name()
                    .unwrap_or_else(|| self.fallback_binding_name(binding));
                let lhs_loc = self.ensure_local_for_binding(binding, debug_name, lhs_ty.clone());

                log::debug!("  EMIT: ${} = ${}", lhs_loc, rhs_loc);
                self.set_local(
                    lhs_loc,
                    lir::Atom::new(lir::Variable::Local(rhs_loc)).into(),
                );
                Ok(())
            }
            Pattern::Deref(inner) => {
                let Some(rhs_loc) = rhs_loc else {
                    log::debug!("  SKIP assign: rhs is unit");
                    return Ok(());
                };

                let lhs_ty = self.ty_of(lhs_pat.id);
                // Look up binding at the deref pattern's NodeId (lhs_pat.id),
                // which is where type lowering recorded it.
                let binding = self.binding_for_node(inner.id).unwrap_or_else(|| {
                    panic!(
                        "missing binding for pattern {:#x} ({})",
                        lhs_pat.id, lhs_pat
                    )
                });

                let debug_name = inner
                    .value
                    .path
                    .name()
                    .unwrap_or_else(|| self.fallback_binding_name(binding));
                let lhs_loc = self.ensure_local_for_binding(binding, debug_name, lhs_ty.clone());

                log::debug!("  EMIT: *${} = ${}", lhs_loc, rhs_loc);
                self.push(lir::Store::new(
                    lir::Variable::Local(lhs_loc),
                    lir::Atom::new(lir::Variable::Local(rhs_loc)).into(),
                    0,
                ));
                Ok(())
            }
            Pattern::Dot(base_pat, field_name) => {
                self.emit_field_assign(base_pat.as_ref(), field_name, rhs_loc)
            }
            Pattern::Index(container_pat, index_expr, _) => self.emit_index_assign(
                assign_id,
                container_pat.as_ref(),
                index_expr.as_ref(),
                rhs_val,
                rhs_ty,
                src,
            ),
            Pattern::Missing(_) => todo!("emit_assign_to_pattern: Pattern::Missing"),
            Pattern::Sequence(pats) | Pattern::Tuple(pats) => {
                let Some(rhs_loc) = rhs_loc else {
                    log::debug!("  SKIP destructuring assign: rhs is unit");
                    return Ok(());
                };

                let rhs_tys = variant!(rhs_ty.mono(), if Ty::Tuple(tys)).clone();
                if rhs_tys.len() != pats.len() {
                    panic!(
                        "tuple destructuring assign arity mismatch: lhs={} rhs_ty={}",
                        lhs_pat, rhs_ty
                    );
                }

                for (index, (pat, el_mono)) in pats.iter().zip(rhs_tys.into_iter()).enumerate() {
                    let el_scheme = TyScheme::from_mono(el_mono.clone());

                    let el_tmp = self.local(el_scheme.clone());
                    self.set_local(
                        el_tmp,
                        lir::Extract::new(lir::Variable::Local(rhs_loc), index),
                    );

                    let el_val: lir::Value = lir::Atom::new(lir::Variable::Local(el_tmp)).into();
                    self.emit_assign_to_pattern(
                        assign_id,
                        pat,
                        el_val,
                        el_scheme,
                        Some(el_tmp),
                        src,
                    )?;
                }

                Ok(())
            }
            Pattern::Some(_) => todo!("emit_assign_to_pattern: Pattern::Some"),
        }
    }

    fn emit_tuple(&mut self, ty: &TyScheme, items: &[Node<Expr>]) -> RayResult<lir::Value> {
        let tys = variant!(ty.mono(), if Ty::Tuple(tys));

        // create a new local for the tuple value
        let tuple_loc = self.local(ty.clone());
        if !items.is_empty() {
            // build tuple value with inserts
            for (index, (el, el_ty)) in items.iter().zip(tys.iter().cloned()).enumerate() {
                let el_val = el.lir_gen(self)?;
                let el_loc = self.get_or_set_local(el_val, el_ty.clone().into()).unwrap();

                let insert = lir::Insert::new(
                    lir::Variable::Local(tuple_loc),
                    index,
                    lir::Atom::new(lir::Variable::Local(el_loc)).into(),
                );
                self.push(lir::Inst::Insert(insert));
            }

            Ok(lir::Value::new(lir::Variable::Local(tuple_loc)))
        } else {
            Ok(lir::Value::new(lir::Atom::NilConst))
        }
    }
}

pub type GenResult = lir::Value;

impl LirGen<GenResult> for (&Path, &TyScheme) {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>) -> RayResult<GenResult> {
        let &(path, _) = self;
        let full_name = path.to_string();
        if let Some(&global) = ctx.global_idx.get(&full_name) {
            return Ok(lir::Variable::Global(ctx.path(), global).into());
        }

        panic!(
            "unresolved value path `{}` (expected global)\n  available globals: {:?}",
            full_name,
            ctx.global_idx.keys().collect::<Vec<_>>(),
        )
    }
}

impl LirGen<GenResult> for (&Literal, &TyScheme) {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>) -> RayResult<GenResult> {
        let &(lit, ty_scheme) = self;
        Ok(match lit {
            Literal::Integer {
                value,
                base,
                size,
                signed,
                explicit_sign,
            } => match base {
                IntegerBase::Decimal => {
                    let size = lir::Size::bytes(size.unwrap_or_default() / 8);
                    lir::Value::new(if *signed {
                        let mut c = value.parse::<i64>()?;
                        if let Some(PrefixOp::Negative) = explicit_sign {
                            c *= -1;
                        }
                        lir::Atom::IntConst(c, size)
                    } else {
                        let c = value.parse::<u64>()?;
                        lir::Atom::UintConst(c, size)
                    })
                }
                IntegerBase::Binary => todo!(),
                IntegerBase::Octal => todo!(),
                IntegerBase::Hex => todo!(),
            },
            Literal::Float {
                value,
                size,
                explicit_sign,
            } => {
                let size = lir::Size::bytes(size / 8);
                let mut c = value.parse::<f64>()?;
                if let Some(PrefixOp::Negative) = explicit_sign {
                    c *= -1.0;
                }
                lir::Value::new(lir::Atom::FloatConst(c, size))
            }
            Literal::String(s) => {
                let loc = ctx.emit_string_literal(s);
                lir::Atom::new(lir::Variable::Local(loc)).into()
            }
            Literal::ByteString(_) => todo!(),
            Literal::Byte(_) => todo!(),
            Literal::Char(ch) => lir::Atom::CharConst(*ch).into(),
            Literal::Bool(b) => lir::Atom::BoolConst(*b).into(),
            Literal::UnicodeEscSeq(_) => todo!(),
            Literal::Unit => lir::Value::Empty,
            Literal::Nil => {
                // If this `nil` is used in a `nilable['a]` context, construct
                // an Option-like aggregate `{ is_some = false, payload: 'a }`.
                let ty = ty_scheme.mono();
                if let Some(payload_ty) = ty.nilable_payload() {
                    let loc = ctx.local(ty_scheme.clone());

                    ctx.push(lir::Inst::StructInit(
                        lir::Variable::Local(loc),
                        StructTy {
                            kind: NominalKind::Struct,
                            path: "nilable".into(),
                            ty: ty_scheme.clone(),
                            fields: vec![
                                ("is_some".to_string(), Ty::bool().into()),
                                (
                                    "payload".to_string(),
                                    TyScheme::from_mono(payload_ty.clone()),
                                ),
                            ],
                        },
                    ));

                    // is_some = false
                    let is_some_loc = ctx.local(Ty::bool().into());
                    ctx.set_local(is_some_loc, lir::Atom::BoolConst(false).into());
                    ctx.push(lir::SetField::new(
                        lir::Variable::Local(loc),
                        str!("is_some"),
                        lir::Variable::Local(is_some_loc).into(),
                    ));

                    lir::Variable::Local(loc).into()
                } else {
                    // Fallback: treat as a raw null pointer.
                    lir::Atom::uptr(0).into()
                }
            }
        })
    }
}

impl LirGen<GenResult> for (&Node<&ast::Func>, &TyScheme, Option<&Path>) {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>) -> RayResult<GenResult> {
        let &(func, fn_ty, base_override) = self;

        ctx.with_builder(Builder::new());

        ctx.with_entry_block(|ctx| {
            // add the parameters to the function
            for p in func.sig.params.iter() {
                let path = p.name();
                let binding = ctx
                    .binding_for_node(p.id)
                    .unwrap_or_else(|| panic!("missing binding for param {:#x}", p.id));
                let key = path
                    .name()
                    .unwrap_or_else(|| ctx.fallback_binding_name(binding));
                let ty = ctx.ty_of(p.id);
                ctx.param(binding, key, ty.into_mono());
            }
        });

        let body = func.body.as_ref().unwrap();
        let body_val = if !matches!(body.value, Expr::Block(_)) {
            let (_, value) = ctx.with_new_block(|ctx| body.lir_gen(ctx));
            value?
        } else {
            body.lir_gen(ctx)?
        };

        ctx.with_exit_block(|ctx| {
            log::debug!("[Func::lir_gen] function type = {:?}", fn_ty);
            let (_, _, _, ret_ty) = fn_ty
                .try_borrow_fn()
                .expect(&format!("function type, but found {:?}", fn_ty));
            let value = if !ret_ty.is_unit() {
                let body_ty = ctx.ty_of(body.id);
                let body_loc = ctx.get_or_set_local(body_val, body_ty).unwrap();
                lir::Variable::Local(body_loc).into()
            } else {
                if let Some(i) = body_val.to_inst() {
                    ctx.push(i);
                }
                lir::Value::Empty
            };

            ctx.ret(value);
        });

        let builder = ctx.builder.take().unwrap();
        let (params, locals, blocks, symbols, cfg) = builder.done();

        let base = base_override
            .cloned()
            .unwrap_or_else(|| func.sig.path.value.clone());
        log::debug!("base function path: {}", base);
        log::debug!("function type: {}", fn_ty);
        let name = if !fn_ty.is_polymorphic() {
            mangle::fn_name(&base, fn_ty)
        } else {
            base.clone()
        };

        log::debug!("function name: {}", name);
        let source_id = func.id;
        let mut func = lir::Func::new(
            base.clone(),
            fn_ty.clone(),
            func.sig.modifiers.clone(),
            symbols,
            cfg,
            Some(source_id),
        );
        func.name = name;
        func.params = params;
        func.locals = locals;
        func.blocks = blocks;

        ctx.new_func(func);

        Ok(lir::Value::Empty)
    }
}

impl LirGen<GenResult> for (NodeId, &Call, &Source) {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>) -> RayResult<GenResult> {
        let &(call_expr_id, call, src) = self;
        let callee_is_direct_fn = call
            .callee
            .path()
            .and_then(|_path| ctx.maybe_direct_function(call.callee.id))
            .is_some();
        let mut arg_exprs: Vec<(&Node<Expr>, TyScheme)> = Vec::new();
        let mut base: Option<Path> = if let Expr::Dot(dot) = &call.callee.value {
            let self_ty = ctx.ty_of(dot.lhs.id);
            log::debug!("[Call::lir_gen] type of {}: {}", dot.lhs, self_ty);
            arg_exprs.push((dot.lhs.as_ref(), self_ty));
            Some(dot.rhs.path.clone())
        } else if let Expr::ScopedAccess(scoped_access) = &call.callee.value {
            if let Expr::Type(ty) = &scoped_access.lhs.value {
                let base = ty.value().mono().get_path().without_type_args();
                let member = scoped_access
                    .rhs
                    .value
                    .path
                    .name()
                    .unwrap_or_else(|| scoped_access.rhs.value.to_string());
                Some(base.append(member))
            } else {
                None
            }
        } else if callee_is_direct_fn {
            // Use fully qualified path from name resolution when available,
            // falling back to the raw AST path. Without this, same-module
            // references (e.g. `writev_stdout` called from `print` in core::io)
            // would remain unqualified and fail during monomorphization.
            let resolutions = name_resolutions(ctx.db, call.callee.id.owner.file);
            if let Some(Resolution::Def(target)) = resolutions.get(&call.callee.id) {
                def_path(ctx.db, target.clone()).map(|ip| ip.to_path())
            } else {
                call.callee.path().cloned()
            }
        } else {
            None
        };

        let resolved = call_resolution(ctx.db, call_expr_id);
        let fn_ty = if let Some(resolved) = &resolved {
            let target = resolved.target().expect("call resolution missing target");
            base = Some(
                def_path(ctx.db, target.clone())
                    .expect("missing def_path for call target")
                    .to_path(),
            );
            resolved.callee_ty.clone()
        } else {
            // Use raw_ty_of to get the actual function type, not a handle-wrapped type
            ctx.raw_ty_of(call.callee.id)
        };

        log::debug!("[lir_gen] scheme for call {}: {}", call, fn_ty);
        log::debug!(
            "call: callee id={:#x} function type = {}",
            call.callee.id,
            fn_ty
        );

        let mut evaluated_callee: Option<lir::Value> = None;
        if base.is_none() {
            let value = call.callee.lir_gen(ctx)?;
            evaluated_callee = Some(value);
        }

        for arg in call.args.items.iter() {
            arg_exprs.push((arg, ctx.ty_of(arg.id)));
        }

        let original_poly_ty = resolved
            .as_ref()
            .map(|resolved| resolved.poly_callee_ty.clone())
            .or_else(|| {
                // If no call resolution, try to get the callee's definition scheme
                let resolutions = name_resolutions(ctx.db, call.callee.id.owner.file);
                if let Some(Resolution::Def(target)) = resolutions.get(&call.callee.id) {
                    def_scheme(ctx.db, target.clone())
                } else {
                    None
                }
            });

        // Snapshot instantiated parameter types of the callee after substitution.
        let param_monos = match fn_ty.mono() {
            Ty::Func(params, _) => params.clone(),
            _ => Vec::new(),
        };

        let recv_mode = resolved
            .as_ref()
            .and_then(|r| r.target())
            .map(|target| ctx.recv_mode_for_base(target))
            .unwrap_or_default();

        let fn_name = if resolved.is_none() {
            base.clone().map(|base| {
                if ctx.is_extern(&base) {
                    ctx.extern_link_name(&base).unwrap_or(base)
                } else {
                    mangle::fn_name(&base, &fn_ty)
                }
            })
        } else {
            None
        };

        let is_method_call = matches!(&call.callee.value, Expr::Dot(_));
        let call_args = ctx.build_call_args(is_method_call, recv_mode, arg_exprs, &param_monos)?;

        if let Some(resolved) = &resolved {
            return ctx.emit_resolved_direct_call(resolved, call_args, src);
        }

        if let Some(fn_name) = fn_name {
            log::debug!("poly_ty: {:?}", original_poly_ty);
            ctx.emit_named_direct_call(
                fn_name,
                call_args,
                fn_ty.clone(),
                original_poly_ty.clone(),
                src,
            )
        } else {
            let callee_val = evaluated_callee
                .take()
                .map(Ok)
                .unwrap_or_else(|| call.callee.lir_gen(ctx))?;
            ctx.emit_fnhandle_call(call.callee.id, callee_val, call_args, original_poly_ty, src)
        }
    }
}

impl LirGen<GenResult> for Node<Expr> {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>) -> RayResult<GenResult> {
        let ty = ctx.ty_of(self.id);
        Ok(match &self.value {
            Expr::Path(segments) => {
                // Convert Vec<Node<String>> to Path
                let path = Path::from(segments.iter().map(|s| s.value.clone()).collect::<Vec<_>>());
                if let Some(fn_ty) = ctx.maybe_direct_function(self.id) {
                    let var = ctx.build_fn_handle_for_function(path.clone(), fn_ty);
                    lir::Value::new(var)
                } else {
                    let binding = ctx.binding_for_node(self.id);
                    if let Some(binding) = binding {
                        if let Some(global) = ctx.global_var_for_binding(binding, &path) {
                            return Ok(global.into());
                        }
                        let debug_name = path
                            .name()
                            .unwrap_or_else(|| format!("__local_{}", binding.index));
                        let loc = ctx.ensure_local_for_binding(binding, debug_name, ty.clone());
                        lir::Value::new(lir::Variable::Local(loc))
                    } else {
                        let owner_path = def_path(ctx.db, DefTarget::Workspace(self.id.owner));
                        let source = ctx.srcmap.get_by_id(self.id);
                        let resolutions = name_resolutions(ctx.db, self.id.owner.file);
                        let resolution = resolutions.get(&self.id);
                        panic!(
                            "unresolved Expr::Path `{}`\n  source: {:?}\n  in function: {:?}\n  node_id: {:?}\n  resolution: {:?}\n  ty: {}",
                            path, source, owner_path, self.id, resolution, ty,
                        );
                    }
                }
            }
            Expr::Name(n) => {
                if let Some(fn_ty) = ctx.maybe_direct_function(self.id) {
                    let var = ctx.build_fn_handle_for_function(n.path.clone(), fn_ty);
                    lir::Value::new(var)
                } else {
                    let binding = ctx.binding_for_node(self.id).unwrap_or_else(|| {
                        let src = ctx.srcmap.get_by_id(self.id);
                        panic!(
                            "missing binding for name expr {:?} ({:#x}: {:?})",
                            n, self.id, src
                        )
                    });
                    if let Some(global) = ctx.global_var_for_binding(binding, &n.path) {
                        return Ok(global.into());
                    }
                    let debug_name = n
                        .path
                        .name()
                        .unwrap_or_else(|| format!("__local_{}", binding.index));
                    let loc = ctx.ensure_local_for_binding(binding, debug_name, ty.clone());
                    lir::Value::new(lir::Variable::Local(loc))
                }
            }
            Expr::ScopedAccess(scoped_access) => {
                if let Expr::Type(ty_scheme) = &scoped_access.lhs.value {
                    let base = ty_scheme.value().mono().get_path().without_type_args();
                    let member = scoped_access
                        .rhs
                        .value
                        .path
                        .name()
                        .unwrap_or_else(|| scoped_access.rhs.value.to_string());
                    let path = base.append(member);

                    if let Some(fn_ty) = ctx.maybe_direct_function(self.id) {
                        let var = ctx.build_fn_handle_for_function(path, fn_ty);
                        lir::Value::new(var)
                    } else {
                        // Fallback: treat it as a global value path.
                        (&path, &ty).lir_gen(ctx)?
                    }
                } else {
                    todo!("lir_gen: Expr::ScopedAccess: {}", self.value)
                }
            }
            Expr::Pattern(p) => {
                // `Expr::Pattern` carries a `Pattern` (not a `Node<Pattern>`), so it does not
                // have stable node ids for its interior. Lower it by converting to an equivalent
                // expression tree, which preserves any existing node ids (e.g. deref name ids).
                let expr_value: Expr = <Pattern as Into<Expr>>::into(p.clone());
                let expr: Node<Expr> = Node::with_id(self.id, expr_value);
                expr.lir_gen(ctx)?
            }
            Expr::Literal(lit) => (lit, &ty).lir_gen(ctx)?,
            Expr::Paren(ex) | Expr::TypeAnnotated(ex, _) => ex.lir_gen(ctx)?,
            Expr::New(new) => {
                let count = match &new.count {
                    Some(c) => {
                        let ty = ctx.ty_of(c.id);
                        let value = c.lir_gen(ctx)?;
                        lir::Variable::Local(ctx.get_or_set_local(value, ty).unwrap()).into()
                    }
                    _ => lir::Atom::uptr(1),
                };
                let ty = resolved_ty(ctx.db, new.ty.id).unwrap_or_else(|| new.ty.clone_value());
                lir::Malloc::new(ty.into(), count)
            }
            Expr::Cast(c) => {
                let src = c.lhs.lir_gen(ctx)?;
                let lhs_ty = ctx.ty_of(c.lhs.id);
                let loc = ctx.get_or_set_local(src, lhs_ty).unwrap();
                let rhs_ty = resolved_ty(ctx.db, c.ty.root_id().unwrap())
                    .unwrap_or_else(|| c.ty.deref().clone());
                lir::Cast::new(lir::Variable::Local(loc), rhs_ty)
            }
            Expr::Range(range) => {
                // create a `range` struct
                //  - start: T
                //  - end: T
                //  - inclusive: bool
                let loc = ctx.local(ty.clone());
                let el_ty = ctx.ty_of(range.start.id);

                let range_target = resolve_builtin(ctx.db, ctx.file_id, "range".to_string())
                    .expect("range type not in scope");
                let range_fqn = def_path(ctx.db, range_target).expect("missing def_path for range");

                ctx.push(lir::Inst::StructInit(
                    lir::Variable::Local(loc),
                    StructTy {
                        kind: NominalKind::Struct,
                        path: range_fqn,
                        ty: Ty::range(el_ty.mono().clone()).into(),
                        fields: vec![
                            ("start".to_string(), el_ty.clone()),
                            ("end".to_string(), el_ty.clone()),
                            ("inclusive".to_string(), Ty::bool().into()),
                        ],
                    },
                ));

                // store the start value
                let start_val = range.start.lir_gen(ctx)?;
                let start_loc = ctx.get_or_set_local(start_val, el_ty.clone()).unwrap();

                ctx.push(lir::SetField::new(
                    lir::Variable::Local(loc),
                    str!("start"),
                    lir::Variable::Local(start_loc).into(),
                ));

                // store the end value
                let end_val = range.end.lir_gen(ctx)?;
                let end_loc = ctx.get_or_set_local(end_val, el_ty.clone()).unwrap();
                ctx.push(lir::SetField::new(
                    lir::Variable::Local(loc),
                    str!("end"),
                    lir::Variable::Local(end_loc).into(),
                ));

                // store the inclusive flag
                let bool_loc = ctx.local(Ty::bool().into());
                ctx.set_local(
                    bool_loc,
                    lir::Atom::UintConst(
                        if matches!(range.limits, RangeLimits::Inclusive) {
                            1
                        } else {
                            0
                        },
                        lir::Size::bytes(1),
                    )
                    .into(),
                );

                ctx.push(lir::SetField::new(
                    lir::Variable::Local(loc),
                    str!("inclusive"),
                    lir::Variable::Local(bool_loc).into(),
                ));

                lir::Atom::new(lir::Variable::Local(loc)).into()
            }
            Expr::Ref(rf) => {
                // &expr has type *T, recover T
                let pointee_ty = variant!(ty.mono(), if Ty::Ref(ty));

                // generate the value for the expression
                let (value, offset) = match &rf.expr.as_ref().value {
                    Expr::Dot(dot) => {
                        let lhs_val = dot.lhs.lir_gen(ctx)?;
                        let lhs_ty = ctx.ty_of(dot.lhs.id);
                        let lhs_loc = ctx.get_or_set_local(lhs_val, lhs_ty.clone()).unwrap();

                        let offset =
                            lir::LeaOffset::Field(lhs_ty.clone(), dot.rhs.path.to_short_name());

                        (
                            lir::Value::Atom(lir::Variable::Local(lhs_loc).into()),
                            offset,
                        )
                    }
                    _ => (rf.expr.lir_gen(ctx)?, lir::LeaOffset::zero()),
                };

                let var = if let Some(var) = value.var() {
                    // if the value is already a variable, use it directly
                    var.clone()
                } else {
                    // otherwise create a new local
                    let loc = ctx
                        .get_or_set_local(value, pointee_ty.as_ref().clone().into())
                        .unwrap();
                    lir::Variable::Local(loc)
                };

                lir::Lea::new(var, offset)
            }
            Expr::Deref(deref) => {
                // `*E` — the inner expression E has type *T (or rawptr[T]), the whole deref has type T.
                // Allocate the temp for E using its OWN type (*T/rawptr[T]), not the outer T.
                let ptr_ty = ctx.ty_of(deref.expr.id); // *T/rawptr[T]
                let value = deref.expr.lir_gen(ctx)?;
                let loc = ctx.get_or_set_local(value, ptr_ty).unwrap();
                let src = lir::Variable::Local(loc);

                lir::Load::new(src, lir::Size::zero())
            }
            Expr::List(list) => {
                let item_count = list.items.len();
                let capacity = (item_count * 3) as u64;

                // allocate memory for the values
                let el_ty = ty
                    .mono()
                    .type_argument_at(0)
                    .unwrap_or_else(|| panic!("expected list to have element type param: {}", ty));

                let values_loc = ctx.local(Ty::ref_of(el_ty.clone()).into());
                let values_ptr = lir::Malloc::new(el_ty.clone().into(), lir::Atom::uptr(capacity));
                ctx.set_local(values_loc, values_ptr.into());

                let mut offset: usize = 0;
                for item in list.items.iter() {
                    let item_val = item.lir_gen(ctx)?;
                    let item_ty = ctx.ty_of(item.id);
                    if let Some(item_loc) = ctx.get_or_set_local(item_val, item_ty) {
                        ctx.push(lir::Store::new(
                            lir::Variable::Local(values_loc),
                            lir::Variable::Local(item_loc).into(),
                            offset,
                        ));
                    }

                    offset += 1;
                }

                let list_loc = ctx.local(ty.clone());
                let list_target = resolve_builtin(ctx.db, ctx.file_id, "list".to_string())
                    .expect("list type not in scope");
                let list_fqn = def_path(ctx.db, list_target).expect("missing def_path for list");

                ctx.push(lir::Inst::StructInit(
                    lir::Variable::Local(list_loc),
                    StructTy {
                        kind: NominalKind::Struct,
                        path: list_fqn.clone(),
                        ty: Ty::proj(list_fqn, vec![el_ty.clone()]).into(),
                        fields: vec![
                            ("values".to_string(), Ty::ref_of(el_ty.clone()).into()),
                            ("len".to_string(), Ty::uint().into()),
                            ("capacity".to_string(), Ty::uint().into()),
                        ],
                    },
                ));

                // store the values ptr
                ctx.push(lir::SetField::new(
                    lir::Variable::Local(list_loc),
                    str!("values"),
                    lir::Variable::Local(values_loc).into(),
                ));

                // store the length
                ctx.push(lir::SetField::new(
                    lir::Variable::Local(list_loc),
                    str!("len"),
                    lir::Atom::uptr(item_count as u64).into(),
                ));

                // store the capacity
                ctx.push(lir::SetField::new(
                    lir::Variable::Local(list_loc),
                    str!("capacity"),
                    lir::Atom::uptr(capacity as u64).into(),
                ));

                lir::Variable::Local(list_loc).into()
            }
            Expr::Curly(curly) => {
                let loc = ctx.local(ty.clone());
                let fields = curly
                    .elements
                    .iter()
                    .map(|elem| {
                        let (name, expr) = variant!(&elem.value, if CurlyElement::Labeled(x, y));
                        let elem_ty = ctx.ty_of(expr.id);
                        (name.path.name().unwrap(), elem_ty)
                    })
                    .collect();

                // Curly expressions are only used for struct initialization
                let kind = NominalKind::Struct;
                ctx.push(lir::Inst::StructInit(
                    lir::Variable::Local(loc),
                    StructTy {
                        kind,
                        path: ty.mono().item_path().cloned().unwrap(),
                        ty: ty.clone(),
                        fields,
                    },
                ));

                let mut field_insts = vec![];
                for field in curly.elements.iter() {
                    let (name, field_value) =
                        variant!(&field.value, if CurlyElement::Labeled(x, y));
                    let field_ty = ctx.ty_of(field_value.id);
                    let val = field_value.lir_gen(ctx)?;
                    field_insts.push((val, name.clone(), field_ty));
                }

                for (val, name, ty) in field_insts {
                    if let Some(field_loc) = ctx.get_or_set_local(val, ty) {
                        ctx.push(lir::SetField::new(
                            lir::Variable::Local(loc),
                            name.path.name().unwrap(),
                            lir::Variable::Local(field_loc).into(),
                        ));
                    }
                }

                lir::Variable::Local(loc).into()
            }
            Expr::Dict(dict) => {
                // Dict literals must be built via the dict API (with_capacity + insert)
                // so we do not bake any internal representation assumptions into codegen.
                let src = ctx.srcmap.get(self);
                let item_count = dict.entries.len();

                let dict_mono = ty.mono().clone();
                let dict_base = dict_mono.get_path().without_type_args();
                let key_mono = dict_mono
                    .type_argument_at(0)
                    .unwrap_or_else(|| panic!("expected dict to have key type param: {}", ty));
                let value_mono = dict_mono
                    .type_argument_at(1)
                    .unwrap_or_else(|| panic!("expected dict to have value type param: {}", ty));

                // tmp = dict.with_capacity(item_count)
                let cap_loc = ctx.local(Ty::uint().into());
                ctx.set_local(cap_loc, lir::Atom::uptr(item_count as u64).into());

                let with_capacity_base = dict_base.append("with_capacity");
                let with_capacity_ty =
                    TyScheme::from_mono(Ty::func(vec![Ty::uint()], dict_mono.clone()));
                let with_capacity_name = mangle::fn_name(&with_capacity_base, &with_capacity_ty);
                let init_val = ctx.emit_named_direct_call(
                    with_capacity_name,
                    vec![lir::Variable::Local(cap_loc)],
                    with_capacity_ty.clone(),
                    Some(with_capacity_ty),
                    &src,
                )?;
                let dict_loc = ctx
                    .get_or_set_local(init_val, ty.clone())
                    .expect("dict.with_capacity should not be unit");

                // tmp.insert(k, v)
                let insert_base = dict_base.append("insert");
                let insert_ret = Ty::nilable(value_mono.clone());
                let insert_recv_param = Ty::ref_of(dict_mono.clone());
                let insert_fn_ty = TyScheme::from_mono(Ty::func(
                    vec![
                        insert_recv_param.clone(),
                        key_mono.clone(),
                        value_mono.clone(),
                    ],
                    insert_ret,
                ));
                let insert_name = mangle::fn_name(&insert_base, &insert_fn_ty);

                let recv_val: lir::Value = lir::Variable::Local(dict_loc).into();
                let recv_var = ctx
                    .maybe_coerce_receiver_arg(recv_val, &ty, &insert_recv_param, ReceiverMode::Ptr)
                    .unwrap_or_else(|| {
                        panic!(
                            "could not build receiver arg for dict.insert: dict_ty={}",
                            ty
                        )
                    });

                for (key, value) in dict.entries.iter() {
                    let key_scheme = ctx.ty_of(key.id);
                    let key_val = key.lir_gen(ctx)?;
                    let key_var = ctx.value_to_local_or_unit(key_val, key_scheme);

                    let value_scheme = ctx.ty_of(value.id);
                    let value_val = value.lir_gen(ctx)?;
                    let value_var = ctx.value_to_local_or_unit(value_val, value_scheme);

                    let call_val = ctx.emit_named_direct_call(
                        insert_name.clone(),
                        vec![recv_var.clone(), key_var, value_var],
                        insert_fn_ty.clone(),
                        Some(insert_fn_ty.clone()),
                        &src,
                    )?;
                    if let Some(inst) = call_val.to_inst() {
                        ctx.push(inst);
                    }
                }

                lir::Variable::Local(dict_loc).into()
            }
            Expr::Block(block) => match block.stmts.split_last() {
                Some((last, rest)) => {
                    for stmt in rest {
                        let value = stmt.lir_gen(ctx)?;
                        if let Some(i) = value.to_inst() {
                            ctx.push(i);
                        }
                    }

                    last.lir_gen(ctx)?
                }
                None => lir::Value::Empty,
            },
            Expr::Boxed(boxed) => {
                let ptr_loc = ctx.local(ty.clone());
                let pointee_ty = variant!(ty.mono(), if Ty::Ref(p));
                let ptr_malloc =
                    lir::Malloc::new(pointee_ty.as_ref().clone().into(), lir::Atom::uptr(1));

                ctx.set_local(ptr_loc, ptr_malloc);
                let value = boxed.inner.lir_gen(ctx)?;
                ctx.push(lir::Store::new(lir::Variable::Local(ptr_loc), value, 0));

                lir::Variable::Local(ptr_loc).into()
            }
            Expr::Assign(assign) => {
                let src = ctx.srcmap.get(self);
                ctx.emit_assign_expr(self.id, assign, &src)?
            }
            Expr::Func(_) => todo!(),
            Expr::Dot(dot) => {
                let lhs_val = dot.lhs.lir_gen(ctx)?;
                let lhs_ty = ctx.ty_of(dot.lhs.id);
                let lhs_loc = ctx.get_or_set_local(lhs_val, lhs_ty.clone()).unwrap();

                lir::GetField {
                    src: lir::Variable::Local(lhs_loc),
                    field: dot.rhs.path.name().unwrap(),
                }
                .into()
            }
            Expr::Call(call) => {
                let src = ctx.srcmap.get(self);
                (self.id, call, &src).lir_gen(ctx)?
            }
            Expr::BinOp(binop) => {
                // Pass the expression node's ID (self.id), not the operator token's ID (binop.op.id),
                // because method_resolutions is keyed by the BinOp expression node.
                ctx.call_from_op(self.id, &[binop.lhs.as_ref(), binop.rhs.as_ref()])?
            }
            Expr::NilCoalesce(nc) => {
                // Nil-coalescing: `lhs else rhs`
                //
                // 1. Evaluate `lhs` (nilable['a]) into a local
                // 2. Extract `is_some` field as the branch condition
                // 3. Then-branch: extract `payload` field (the unwrapped value)
                // 4. Else-branch: evaluate `rhs`
                // 5. Merge both branches into the result local

                let lhs_ty = ctx.ty_of(nc.lhs.id);
                let lhs_val = nc.lhs.lir_gen(ctx)?;
                let lhs_loc = ctx.get_or_set_local(lhs_val, lhs_ty.clone()).unwrap();

                // Extract `is_some` field and branch on it
                let cond_label = ctx.new_block();
                let cond_loc = ctx.with_block(cond_label, |ctx| {
                    ctx.block().markers_mut().push(lir::ControlMarker::If);
                    let is_some_val: lir::Value = lir::GetField {
                        src: lir::Variable::Local(lhs_loc),
                        field: str!("is_some"),
                    }
                    .into();
                    ctx.get_or_set_local(is_some_val, Ty::bool().into())
                        .unwrap()
                });

                ctx.goto(cond_label);

                // Then-branch: extract the payload
                let payload_ty = lhs_ty
                    .mono()
                    .nilable_payload()
                    .cloned()
                    .map(TyScheme::from_mono)
                    .unwrap_or_else(|| ty.clone());

                let then_label = ctx.new_block();
                let (then_val, then_end) = ctx.with_block_capture(then_label, |_ctx| {
                    let payload_val: lir::Value = lir::GetField {
                        src: lir::Variable::Local(lhs_loc),
                        field: str!("payload"),
                    }
                    .into();
                    RayResult::Ok(payload_val)
                });
                let then_val = then_val?;

                // Else-branch: evaluate rhs
                let else_label = ctx.new_block();
                let (else_val, else_end) =
                    ctx.with_block_capture(else_label, |ctx| RayResult::Ok(nc.rhs.lir_gen(ctx)?));
                let else_val = else_val?;

                // Create result local and store from both branches
                let result_loc = ctx.local(ty.clone());
                ctx.with_block(then_end, |ctx| {
                    if let Some(loc) = ctx.get_or_set_local(then_val, payload_ty) {
                        ctx.set_local(
                            result_loc,
                            lir::Atom::Variable(lir::Variable::Local(loc)).into(),
                        );
                    }
                });
                ctx.with_block(else_end, |ctx| {
                    if let Some(loc) = ctx.get_or_set_local(else_val, ty.clone()) {
                        ctx.set_local(
                            result_loc,
                            lir::Atom::Variable(lir::Variable::Local(loc)).into(),
                        );
                    }
                });

                // Wire up the control flow
                ctx.with_block(cond_label, |ctx| {
                    ctx.cond(cond_loc, then_label, else_label);
                });

                let end_label = ctx.new_block();
                ctx.with_block(then_end, |ctx| ctx.goto(end_label));
                ctx.with_block(else_end, |ctx| ctx.goto(end_label));

                ctx.use_block(end_label);
                ctx.block()
                    .markers_mut()
                    .push(lir::ControlMarker::End(cond_label));

                lir::Atom::Variable(lir::Variable::Local(result_loc)).into()
            }
            Expr::FString(fstr) => {
                let src = ctx.srcmap.get(self);
                let string_scheme = TyScheme::from_mono(Ty::Const(
                    resolve_builtin(ctx.db, ctx.file_id, "string".to_string())
                        .and_then(|target| def_path(ctx.db, target))
                        .expect("string type not found"),
                ));

                let needs_to_str = fstr.parts.iter().any(|p| matches!(p, FStringPart::Expr(_)));
                let needs_concat = fstr.parts.len() > 1;

                let to_str_fqn = if needs_to_str {
                    Some(
                        resolve_builtin(ctx.db, ctx.file_id, "ToStr".to_string())
                            .and_then(|target| def_path(ctx.db, target))
                            .expect("ToStr trait not found"),
                    )
                } else {
                    None
                };

                let add_fqn = if needs_concat {
                    Some(
                        resolve_builtin(ctx.db, ctx.file_id, "Add".to_string())
                            .and_then(|target| def_path(ctx.db, target))
                            .expect("Add trait not found"),
                    )
                } else {
                    None
                };

                // Convert each part to a string-typed local
                let mut string_locs: Vec<usize> = Vec::new();
                for part in &fstr.parts {
                    match part {
                        FStringPart::Literal(s) => {
                            string_locs.push(ctx.emit_string_literal(s));
                        }
                        FStringPart::Expr(expr) => {
                            let expr_scheme = ctx.ty_of(expr.id);
                            let expr_val = expr.lir_gen(ctx)?;
                            let expr_loc = ctx
                                .get_or_set_local(expr_val, expr_scheme.clone())
                                .unwrap_or_else(|| panic!("expected non-unit f-string expression"));

                            // Call ToStr::to_str() on the expression
                            let to_str_callee_ty = TyScheme::from_mono(Ty::func(
                                vec![expr_scheme.mono().clone()],
                                string_scheme.mono().clone(),
                            ));
                            let str_loc = ctx
                                .emit_trait_method_call_with_recv_local(
                                    to_str_fqn.as_ref().unwrap(),
                                    "to_str",
                                    expr_loc,
                                    expr_scheme,
                                    to_str_callee_ty,
                                    &src,
                                )?
                                .unwrap_or_else(|| {
                                    panic!("expected non-unit return from to_str()")
                                });
                            string_locs.push(str_loc);
                        }
                    }
                }

                if string_locs.is_empty() {
                    // Empty f-string: emit ""
                    let loc = ctx.emit_string_literal("");
                    lir::Atom::Variable(lir::Variable::Local(loc)).into()
                } else {
                    let mut acc_loc = string_locs[0];
                    let string_mono = string_scheme.mono().clone();
                    for &next_loc in &string_locs[1..] {
                        let add_callee_ty = TyScheme::from_mono(Ty::func(
                            vec![string_mono.clone(), string_mono.clone()],
                            string_mono.clone(),
                        ));
                        let resolved = ctx
                            .resolve_trait_method_direct_call(
                                add_fqn.as_ref().unwrap(),
                                "+",
                                add_callee_ty,
                            )
                            .unwrap_or_else(|| {
                                panic!("could not resolve Add::+ for string concat")
                            });

                        let call_args = vec![
                            lir::Variable::Local(acc_loc),
                            lir::Variable::Local(next_loc),
                        ];
                        let concat_val =
                            ctx.emit_resolved_direct_call(&resolved, call_args, &src)?;
                        acc_loc = ctx
                            .get_or_set_local(concat_val, string_scheme.clone())
                            .unwrap_or_else(|| {
                                panic!("expected non-unit return from string concat")
                            });
                    }
                    lir::Atom::Variable(lir::Variable::Local(acc_loc)).into()
                }
            }
            Expr::Break(ex) => {
                if let Some(_) = ex {
                    todo!()
                } else {
                    if let Some(label) = ctx.control_block {
                        ctx.goto(label);
                    } else {
                        // TODO: should this even be valid if there is no control block?
                        ctx.push(lir::Break::new().into());
                    }
                    lir::Value::Empty
                }
            }
            Expr::Continue => {
                if let Some(label) = ctx.continue_block {
                    ctx.goto(label);
                } else {
                    // TODO: this should be invalid outside loops; fall back to `Break`.
                    ctx.push(lir::Break::new().into());
                }
                lir::Value::Empty
            }
            Expr::Closure(closure) => {
                let captures = ctx.collect_closure_captures(self.id);
                let env_ty = ctx.ensure_closure_env_type(self.id, &captures);
                let fn_name = ctx.lower_closure(self, closure, &captures, &env_ty)?;
                let env = ctx.build_closure_env(&captures, &env_ty)?;
                let fn_ty_with_env = ctx
                    .closure_fn_types
                    .get(&self.id)
                    .expect("missing lowered closure fn type")
                    .clone();
                let closure_value_ty = ctx.ensure_closure_value_type(self.id, &fn_ty_with_env);
                // Closures don't have polymorphic types in Ray
                let handle = ctx.build_closure_value(
                    &closure_value_ty,
                    fn_name,
                    fn_ty_with_env.clone(),
                    env,
                    &env_ty,
                    None,
                )?;
                handle.into()
            }
            Expr::DefaultValue(_) => todo!("lir_gen: Expr::DefaultValue: {}", self.value),
            Expr::For(for_loop) => {
                let src = ctx.srcmap.get(self);

                let iterable_scheme = ctx.ty_of(for_loop.expr.id);
                let iterable_val = for_loop.expr.lir_gen(ctx)?;
                let iterable_loc = ctx
                    .get_or_set_local(iterable_val, iterable_scheme.clone())
                    .unwrap_or_else(|| panic!("expected non-unit iterable expression in `for`"));

                let iterable_trait_fqn =
                    resolve_builtin(ctx.db, ctx.file_id, "Iterable".to_string())
                        .and_then(|target| def_path(ctx.db, target))
                        .expect("Iterable trait not found");
                let iter_trait_fqn = resolve_builtin(ctx.db, ctx.file_id, "Iter".to_string())
                    .and_then(|target| def_path(ctx.db, target))
                    .expect("Iter trait not found");

                let container_mono = iterable_scheme.mono().clone();
                let elem_scheme = ctx.ty_of(for_loop.pat.id);
                let elem_mono = elem_scheme.mono().clone();

                let it_mono = ctx
                    .select_iterable_iterator_ty(&iterable_trait_fqn, &container_mono, &elem_mono)
                    .unwrap_or_else(|| {
                        panic!(
                            "could not select iterator type for `for`: Iterable[{}, _, {}]",
                            container_mono, elem_mono
                        )
                    });
                let it_scheme = TyScheme::from_mono(it_mono.clone());

                // it = (&iterable).iter()
                let iter_callee_ty = TyScheme::from_mono(Ty::func(
                    vec![Ty::ref_of(container_mono.clone())],
                    it_mono.clone(),
                ));
                let it_loc = ctx
                    .emit_trait_method_call_with_recv_local(
                        &iterable_trait_fqn,
                        "iter",
                        iterable_loc,
                        iterable_scheme.clone(),
                        iter_callee_ty,
                        &src,
                    )?
                    .unwrap_or_else(|| panic!("expected non-unit return from `Iterable::iter`"));

                // Pre-allocate the `next()` result local so the body can read it.
                let next_ret_mono = Ty::nilable(elem_mono.clone());
                let next_scheme = TyScheme::from_mono(next_ret_mono.clone());
                let next_loc = ctx.local(next_scheme.clone());

                let prev_control = ctx.control_block;
                let prev_continue = ctx.continue_block;

                let cond_label = ctx.new_block();
                let body_label = ctx.new_block();
                let end_label = ctx.new_block();

                ctx.control_block = Some(end_label);
                ctx.continue_block = Some(cond_label);
                ctx.goto(cond_label);

                ctx.with_block(cond_label, |ctx| -> RayResult<()> {
                    ctx.block().markers_mut().push(lir::ControlMarker::Loop);

                    let next_callee_ty = TyScheme::from_mono(Ty::func(
                        vec![Ty::ref_of(it_mono.clone())],
                        next_ret_mono.clone(),
                    ));
                    let next_call_loc = ctx
                        .emit_trait_method_call_with_recv_local(
                            &iter_trait_fqn,
                            "next",
                            it_loc,
                            it_scheme.clone(),
                            next_callee_ty,
                            &src,
                        )?
                        .unwrap_or_else(|| panic!("expected non-unit return from `Iter::next`"));
                    ctx.set_local(next_loc, lir::Variable::Local(next_call_loc).into());

                    let is_some_val = lir::GetField {
                        src: lir::Variable::Local(next_loc),
                        field: str!("is_some"),
                    }
                    .into();
                    let is_some_loc = ctx
                        .get_or_set_local(is_some_val, Ty::bool().into())
                        .unwrap();
                    ctx.cond(is_some_loc, body_label, end_label);
                    Ok(())
                })?;

                ctx.with_block(body_label, |ctx| -> RayResult<()> {
                    let elem_val = lir::GetField {
                        src: lir::Variable::Local(next_loc),
                        field: str!("payload"),
                    }
                    .into();

                    let handled = ctx.emit_pattern_bind_or_guard(
                        &for_loop.pat,
                        &elem_scheme,
                        elem_val,
                        cond_label,
                        &for_loop.body,
                    )?;
                    if handled {
                        return Ok(());
                    }

                    let body_val = for_loop.body.lir_gen(ctx)?;
                    if let Some(i) = body_val.to_inst() {
                        ctx.push(i);
                    }
                    ctx.goto(cond_label);
                    Ok(())
                })?;

                let after_label = ctx.new_block();
                ctx.with_block(end_label, |ctx| {
                    ctx.goto(after_label);
                });

                ctx.use_block(after_label);
                ctx.block()
                    .markers_mut()
                    .push(lir::ControlMarker::End(cond_label));

                ctx.control_block = prev_control;
                ctx.continue_block = prev_continue;

                lir::Value::Empty
            }
            Expr::If(if_ex) => {
                log::debug!("type of: {}", ty);

                // Optional binding for `if some(name) = expr { ... }`:
                // we record the payload local here so we can bind the inner
                // name in the then-branch.
                let mut some_binding: Option<(LocalBindingId, String, usize)> = None;

                let cond_label = ctx.new_block();
                let cond_loc = ctx.with_block(cond_label, |ctx| {
                    ctx.block().markers_mut().push(lir::ControlMarker::If);
                    // Special-case `if some(pat) = expr { ... }` by lowering
                    // the condition to a check of the `is_some` field on the
                    // `nilable['a]` value produced by `expr`, and, for the
                    // simple `some(name)` case, binding `name` to the payload.
                    let cond_val = match &if_ex.cond.value {
                        Expr::Assign(assign) if matches!(assign.lhs.value, Pattern::Some(_)) => {
                            let rhs_ty = ctx.ty_of(assign.rhs.id);
                            let rhs_val = assign.rhs.lir_gen(ctx)?;
                            let rhs_loc = ctx.get_or_set_local(rhs_val, rhs_ty.clone()).unwrap();

                            if let Pattern::Some(inner_pat) = &assign.lhs.value {
                                let some_binder: Option<(LocalBindingId, String)> = match &inner_pat.value {
                                    Pattern::Name(name) => {
                                        let binding = ctx.binding_for_node(inner_pat.id).unwrap_or_else(|| {
                                            panic!("missing binding for `some(name)` pattern {:#x}", inner_pat.id)
                                        });
                                        let debug_name = name
                                            .path
                                            .name()
                                            .unwrap_or_else(|| ctx.fallback_binding_name(binding));
                                        Some((binding, debug_name))
                                    }
                                    Pattern::Deref(Node { id, value: name }) => {
                                        let binding = ctx.binding_for_node(*id).unwrap_or_else(|| {
                                            panic!(
                                                "missing binding for `some(*name)` pattern {:#x} (name {:#x})",
                                                inner_pat.id, id
                                            )
                                        });
                                        let debug_name = name
                                            .path
                                            .name()
                                            .unwrap_or_else(|| ctx.fallback_binding_name(binding));
                                        Some((binding, debug_name))
                                    }
                                    _ => None,
                                };

                                if let Some((binding, debug_name)) = some_binder {
                                    // The RHS has type `nilable['a]`; extract
                                    // the payload type from it directly.
                                    let payload_mono = rhs_ty
                                        .mono()
                                        .nilable_payload()
                                        .cloned()
                                        .unwrap_or(Ty::Never);
                                    let payload_scheme = TyScheme::from_mono(payload_mono);

                                    let payload_val = lir::GetField {
                                        src: lir::Variable::Local(rhs_loc),
                                        field: str!("payload"),
                                    }
                                    .into();

                                    if let Some(payload_loc) =
                                        ctx.get_or_set_local(payload_val, payload_scheme)
                                    {
                                        some_binding = Some((binding, debug_name, payload_loc));
                                    }
                                }
                            }

                            lir::GetField {
                                src: lir::Variable::Local(rhs_loc),
                                field: str!("is_some"),
                            }
                            .into()
                        }
                        _ => if_ex.cond.lir_gen(ctx)?,
                    };
                    RayResult::Ok(ctx.get_or_set_local(cond_val, Ty::bool().into()).unwrap())
                });

                // in the _current_ block, goto the condition
                ctx.goto(cond_label);

                let then_ty = ctx.ty_of(if_ex.then.id);
                let then_label = ctx.new_block();
                let (then_val, then_end) = ctx.with_block_capture(then_label, |ctx| {
                    // Install the binding for `some(name)` in the then-branch
                    // so that references to `name` see the payload local.
                    if let Some((binding, ref name, payload_loc)) = some_binding {
                        ctx.set_var(binding, name.clone(), payload_loc);
                    }
                    RayResult::Ok(if_ex.then.lir_gen(ctx)?)
                });

                let then_val = then_val?;
                let then_has_value = !matches!(then_val, lir::Value::Empty);
                let else_label = ctx.new_block();
                let (else_val, else_end) = ctx.with_block_capture(else_label, |ctx| {
                    RayResult::Ok(if let Some(else_ex) = if_ex.els.as_deref() {
                        Some(else_ex.lir_gen(ctx)?)
                    } else if !then_ty.is_unit() {
                        Some(lir::Atom::NilConst.into())
                    } else {
                        None
                    })
                });

                // create a local for the result of the if expression
                let if_loc = if !then_ty.is_unit() && then_has_value {
                    let if_loc = ctx.local(ty.clone());
                    ctx.with_block(then_end, |ctx| {
                        ctx.set_local(if_loc, then_val);
                    });

                    if let Some(else_val) = else_val? {
                        ctx.with_block(else_end, |ctx| {
                            ctx.set_local(if_loc, else_val);
                        });
                    }

                    Some(if_loc)
                } else {
                    // Statement `if`: emit side-effecting instructions from both
                    // branches, but do not produce a value.
                    ctx.with_block(then_end, |ctx| {
                        if let Some(i) = then_val.to_inst() {
                            ctx.push(i);
                        }
                    });
                    if let Some(ev) = else_val? {
                        ctx.with_block(else_end, |ctx| {
                            if let Some(i) = ev.to_inst() {
                                ctx.push(i);
                            }
                        });
                    }
                    None
                };

                // branch to the then and else blocks
                let cond_loc = cond_loc?;
                ctx.with_block(cond_label, |ctx| ctx.cond(cond_loc, then_label, else_label));

                // create the end label
                let end_label = ctx.new_block();

                // create branches from the if and then blocks to the end block
                ctx.with_block(then_end, |ctx| ctx.goto(end_label));
                ctx.with_block(else_end, |ctx| ctx.goto(end_label));

                // use the end block for the next instructions
                ctx.use_block(end_label);
                ctx.block()
                    .markers_mut()
                    .push(lir::ControlMarker::End(cond_label));

                if_loc
                    .map(|l| lir::Atom::Variable(lir::Variable::Local(l)).into())
                    .unwrap_or_default()
            }
            Expr::Index(index) => {
                let resolved = call_resolution(ctx.db, self.id).unwrap_or_else(|| {
                    panic!("missing call resolution for index expr {:#x}", self.id)
                });

                let param_monos = match resolved.callee_ty.mono() {
                    Ty::Func(params, _) => params.clone(),
                    _ => Vec::new(),
                };

                let target = resolved.target().expect("call resolution missing target");
                let recv_mode = ctx.recv_mode_for_base(target);
                let lhs_ty = ctx.ty_of(index.lhs.id);
                let index_ty = ctx.ty_of(index.index.id);
                let call_args = ctx.build_call_args(
                    true,
                    recv_mode,
                    vec![
                        (index.lhs.as_ref(), lhs_ty),
                        (index.index.as_ref(), index_ty),
                    ],
                    &param_monos,
                )?;

                let src = ctx.srcmap.get(self);
                ctx.emit_resolved_direct_call(&resolved, call_args, &src)?
            }
            Expr::Labeled(_, _) => todo!("lir_gen: Expr::Labeled: {}", self.value),
            Expr::Loop(_) => todo!("lir_gen: Expr::Loop: {}", self.value),
            Expr::Return(ret) => {
                if let Some(ex) = ret {
                    let val = ex.lir_gen(ctx)?;
                    ctx.ret(val);
                } else {
                    // Bare `return` in a function whose Ray return type is `unit`.
                    ctx.ret(lir::Value::Empty);
                }
                lir::Value::Empty
            }
            Expr::Sequence(seq) => ctx.emit_tuple(&ty, &seq.items)?,
            Expr::Set(set) => {
                // Set literals must be built via the set API (with_capacity + insert)
                // so we do not bake any internal representation assumptions into codegen.
                let src = ctx.srcmap.get(self);
                let item_count = set.items.len();

                let set_mono = ty.mono().clone();
                let set_base = set_mono.get_path().without_type_args();
                let elem_mono = set_mono
                    .type_argument_at(0)
                    .unwrap_or_else(|| panic!("expected set to have element type param: {}", ty));

                // tmp = set.with_capacity(item_count)
                let cap_loc = ctx.local(Ty::uint().into());
                ctx.set_local(cap_loc, lir::Atom::uptr(item_count as u64).into());

                let with_capacity_base = set_base.append("with_capacity");
                let with_capacity_ty =
                    TyScheme::from_mono(Ty::func(vec![Ty::uint()], set_mono.clone()));
                let with_capacity_name = mangle::fn_name(&with_capacity_base, &with_capacity_ty);
                let init_val = ctx.emit_named_direct_call(
                    with_capacity_name,
                    vec![lir::Variable::Local(cap_loc)],
                    with_capacity_ty.clone(),
                    Some(with_capacity_ty),
                    &src,
                )?;
                let set_loc = ctx
                    .get_or_set_local(init_val, ty.clone())
                    .expect("set.with_capacity should not be unit");

                // tmp.insert(x)
                let insert_base = set_base.append("insert");
                let insert_recv_param = Ty::ref_of(set_mono.clone());
                let insert_fn_ty = TyScheme::from_mono(Ty::func(
                    vec![insert_recv_param.clone(), elem_mono.clone()],
                    Ty::bool(),
                ));
                let insert_name = mangle::fn_name(&insert_base, &insert_fn_ty);

                let recv_val: lir::Value = lir::Variable::Local(set_loc).into();
                let recv_var = ctx
                    .maybe_coerce_receiver_arg(recv_val, &ty, &insert_recv_param, ReceiverMode::Ptr)
                    .unwrap_or_else(|| {
                        panic!("could not build receiver arg for set.insert: set_ty={}", ty)
                    });

                for item in set.items.iter() {
                    let item_scheme = ctx.ty_of(item.id);
                    let item_val = item.lir_gen(ctx)?;
                    let item_var = ctx.value_to_local_or_unit(item_val, item_scheme);

                    let call_val = ctx.emit_named_direct_call(
                        insert_name.clone(),
                        vec![recv_var.clone(), item_var],
                        insert_fn_ty.clone(),
                        Some(insert_fn_ty.clone()),
                        &src,
                    )?;
                    if let Some(inst) = call_val.to_inst() {
                        ctx.push(inst);
                    }
                }

                lir::Variable::Local(set_loc).into()
            }
            Expr::Tuple(tuple) => ctx.emit_tuple(&ty, &tuple.seq.items)?,
            Expr::Type(ty) => {
                let scheme = resolved_ty(ctx.db, ty.root_id().unwrap())
                    .map(|ty| TyScheme::from_mono(ty))
                    .unwrap_or_else(|| ty.clone_value());
                lir::Value::Type(scheme)
            }
            Expr::UnaryOp(unop) => {
                // Pass the expression node's ID (self.id), not the operator token's ID (unop.op.id),
                // because method_resolutions is keyed by the UnaryOp expression node.
                ctx.call_from_op(self.id, &[unop.expr.as_ref()])?
            }
            Expr::Unsafe(_) => todo!("lir_gen: Expr::Unsafe: {}", self.value),
            Expr::While(while_stmt) => {
                let cond_label = ctx.new_block();
                let body_label = ctx.new_block();
                let end_label = ctx.new_block();

                let prev_control = ctx.control_block;
                let prev_continue = ctx.continue_block;
                ctx.control_block = Some(end_label);
                ctx.continue_block = Some(cond_label);

                ctx.with_block(cond_label, |ctx| {
                    ctx.block().markers_mut().push(lir::ControlMarker::Loop);

                    let cond_val = while_stmt.cond.lir_gen(ctx)?;
                    let cond_loc = ctx.get_or_set_local(cond_val, Ty::bool().into()).unwrap();
                    ctx.cond(cond_loc, body_label, end_label);

                    ctx.with_block(body_label, |ctx| {
                        let body_val = while_stmt.body.lir_gen(ctx)?;
                        if let Some(i) = body_val.to_inst() {
                            ctx.push(i);
                        }
                        ctx.goto(cond_label);
                        RayResult::Ok(())
                    })?;

                    RayResult::Ok(())
                })?;

                // `end_label` is the `break` target for this loop. Emit an explicit
                // branch out of it so `Builder::done()` cannot "fall through" into
                // blocks created inside the loop body (which would re-enter the loop).
                let after_label = ctx.new_block();
                ctx.with_block(end_label, |ctx| {
                    ctx.goto(after_label);
                });

                ctx.use_block(after_label);
                ctx.block()
                    .markers_mut()
                    .push(lir::ControlMarker::End(cond_label));

                ctx.control_block = prev_control;
                ctx.continue_block = prev_continue;

                lir::Value::Empty
            }
            Expr::Some(inner) => {
                // Construct a `nilable['a]` value as an Option-like aggregate:
                // `{ is_some: bool, payload: 'a }`
                let inner_ty = ctx.ty_of(inner.id);
                let loc = ctx.local(ty.clone());

                ctx.push(lir::Inst::StructInit(
                    lir::Variable::Local(loc),
                    StructTy {
                        kind: NominalKind::Struct,
                        path: "nilable".into(),
                        ty: ty.clone(),
                        fields: vec![
                            ("is_some".to_string(), Ty::bool().into()),
                            ("payload".to_string(), inner_ty.clone()),
                        ],
                    },
                ));

                // store is_some = true
                let is_some_loc = ctx.local(Ty::bool().into());
                ctx.set_local(is_some_loc, lir::Atom::BoolConst(true).into());
                ctx.push(lir::SetField::new(
                    lir::Variable::Local(loc),
                    str!("is_some"),
                    lir::Variable::Local(is_some_loc).into(),
                ));

                // store the payload
                let inner_val = inner.lir_gen(ctx)?;
                if let Some(inner_loc) = ctx.get_or_set_local(inner_val, inner_ty) {
                    ctx.push(lir::SetField::new(
                        lir::Variable::Local(loc),
                        str!("payload"),
                        lir::Variable::Local(inner_loc).into(),
                    ));
                }

                lir::Variable::Local(loc).into()
            }
            Expr::Missing(_) => todo!("lir_gen: Expr::Missing: {}", self.value),
        })
    }
}

impl LirGen<GenResult> for Node<Decl> {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>) -> RayResult<GenResult> {
        log::debug!("getting type of {:#x}: {:?}", self.id, self);
        match &self.value {
            Decl::Func(func) => {
                let node = Node::with_id(self.id, func);
                let ty = def_scheme(ctx.db, DefTarget::Workspace(self.id.owner))
                    .unwrap_or_else(|| ctx.raw_ty_of(self.id));
                return (&node, &ty, None).lir_gen(ctx);
            }
            Decl::Mutable(name, modifiers) | Decl::Name(name, modifiers) => {
                if modifiers.contains(&Modifier::Extern) {
                    let has_intrinsic = ctx.srcmap.has_intrinsic(self);
                    let intrinsic_kind = if has_intrinsic {
                        lir::IntrinsicKind::from_path(&name.path)
                    } else {
                        None
                    };
                    let is_mutable = matches!(&self.value, Decl::Mutable(_, _));
                    let ty = ctx.ty_of(name.id);
                    let map_name = name.path.clone();
                    ctx.new_extern(
                        map_name.clone(),
                        map_name,
                        ty,
                        is_mutable,
                        modifiers.clone(),
                        has_intrinsic,
                        intrinsic_kind,
                        None, // No @src support for now
                    );
                } else {
                    todo!("non-extern Mutable/Name declarations")
                }
            }
            Decl::Trait(tr) => {
                for func in tr.fields.iter() {
                    let func = variant!(func.deref(), if Decl::FnSig(f));
                    ctx.add_trait_member(func.path.value.clone());
                }
            }
            Decl::Impl(imp) => {
                if let Some(consts) = &imp.consts {
                    for const_node in consts {
                        let ty = ctx.ty_of(const_node.lhs.id);
                        let name = const_node.lhs.path().unwrap();
                        let init_value = const_node.rhs.lir_gen(ctx)?;
                        ctx.new_global(name, init_value, ty, false);
                    }
                }

                // For trait impls, compute the trait-qualified base path
                // (e.g., core::ToStr) so methods are named core::ToStr::to_str.
                // For inherent impls (impl object), use None to keep the AST path.
                let trait_base: Option<Path> = if !imp.is_object {
                    let impl_target = DefTarget::Workspace(self.id.owner);
                    impl_def(ctx.db, impl_target)
                        .as_ref()
                        .as_ref()
                        .and_then(|def| def.trait_ty.as_ref())
                        .and_then(|trait_ty| trait_ty.item_path())
                        .map(|ip| ip.to_path())
                } else {
                    None
                };

                if let Some(funcs) = &imp.funcs {
                    for decl in funcs {
                        let Decl::Func(func) = &decl.value else {
                            unreachable!("impl funcs should only contain Decl::Func");
                        };
                        let func_node = Node {
                            id: decl.id,
                            value: func,
                        };
                        let ty = def_scheme(ctx.db, DefTarget::Workspace(decl.id.owner))
                            .unwrap_or_else(|| ctx.ty_of(decl.id));

                        // Build trait-qualified method path: trait_path::method_name
                        let base_override = trait_base.as_ref().and_then(|trait_path| {
                            func.sig.path.name().map(|name| trait_path.append(name))
                        });

                        log::debug!(
                            "[lir_gen] generate impl func: ty = {}, base_override = {:?}, sig = {:?}",
                            ty,
                            base_override,
                            func.sig
                        );
                        (&func_node, &ty, base_override.as_ref()).lir_gen(ctx)?;
                    }
                }
            }
            Decl::Declare(_) => todo!(),
            Decl::FnSig(sig) => {
                if sig.modifiers.contains(&Modifier::Extern) {
                    let has_intrinsic = ctx.srcmap.has_intrinsic(self);
                    log::debug!(
                        "[Decl::lir_gen] extern FnSig has_intrinsic={}: {:?}",
                        has_intrinsic,
                        self
                    );
                    let intrinsic_kind = if has_intrinsic {
                        lir::IntrinsicKind::from_path(&sig.path.value)
                    } else {
                        None
                    };
                    let ty = def_scheme(ctx.db, DefTarget::Workspace(self.id.owner))
                        .unwrap_or_else(|| ctx.ty_of(self.id));
                    let map_name = sig.path.value.clone();
                    let link_name = sig
                        .path
                        .name()
                        .map(|n| Path::from(n))
                        .unwrap_or_else(Path::new);
                    ctx.new_extern(
                        map_name,
                        link_name,
                        ty,
                        false,
                        sig.modifiers.clone(),
                        has_intrinsic,
                        intrinsic_kind,
                        None, // No @src support for now
                    );
                }
                // Non-extern FnSig (trait method signatures) don't generate LIR
            }
            Decl::TypeAlias(_, _) | Decl::Struct(_) => {}
            Decl::FileMain(stmts) => {
                // FileMain statements are generated via the main entry point
                for stmt in stmts {
                    stmt.lir_gen(ctx)?;
                }
            }
        }

        Ok(lir::Value::Empty)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_frontend::{
        queries::{
            libraries::LoadedLibraries,
            workspace::{CompilerOptions, FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };
    use ray_shared::{
        file_id::FileId,
        pathlib::{FilePath, ModulePath},
        ty::Ty,
        utils::map_join,
    };

    use ray_lir::{ControlMarker, Inst, Value};

    use crate::lir::generate;

    struct TestWorkspaceFile {
        filepath: String,
        module_path: String,
        source: String,
    }

    fn setup_test_workspace(src: &str) -> (Database, FileId) {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();

        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        workspace.entry = Some(file_id);

        db.set_input::<WorkspaceSnapshot>((), workspace);
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: true });
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());
        FileSource::new(&db, file_id, src.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );
        (db, file_id)
    }

    fn setup_test_workspace_with_files(files: Vec<TestWorkspaceFile>) -> (Database, Vec<FileId>) {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();

        let mut file_ids = vec![];
        for (idx, file) in files.into_iter().enumerate() {
            let fp = FilePath::from(file.filepath);
            let mp = ModulePath::from(file.module_path);
            let file_id = workspace.add_file(fp.clone(), mp.clone());
            if idx == 0 {
                workspace.entry = Some(file_id);
            }

            FileSource::new(&db, file_id, file.source.to_string());
            FileMetadata::new(&db, file_id, fp, mp);
            file_ids.push(file_id);
        }

        db.set_input::<WorkspaceSnapshot>((), workspace);
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: true });
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());
        (db, file_ids)
    }

    #[test]
    fn generates_simple_function() {
        let src = r#"
            fn id(x: u32) -> u32 { x }
            pub fn main() -> u32 { id(1u32) }
        "#;

        let (db, _file_id) = setup_test_workspace(src);
        let gen_result = generate(&db, false);
        if let Err(err) = gen_result {
            panic!("{:?}", err);
        }

        let prog = gen_result.unwrap();
        assert_eq!(
            prog.funcs.len(),
            4, // _start, module main, id, and user main
            "expected 4 functions, found {}: [{}]",
            prog.funcs.len(),
            map_join(&prog.funcs, ", ", |f| format!("{:#}", f.name))
        );

        let id_func = prog
            .funcs
            .iter()
            .find(|f| &f.name.with_names_only().to_short_name() == "id");
        assert!(id_func.is_some());
    }

    #[test]
    fn generates_closure_and_struct() {
        let src = r#"
@intrinsic extern fn u32_add(a: u32, b: u32) -> u32

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

impl Add[u32, u32, u32] {
    fn +(lhs: u32, rhs: u32) -> u32 => u32_add(lhs, rhs)
}

struct Pair { x: u32, y: u32 }

pub fn main() -> u32 {
    p = Pair { x: 1u32, y: 2u32 }
    add = (a, b) => a + b
    add(p.x, p.y)
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        let mut saw_pair_literal = false;
        let mut saw_closure_call = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                match inst {
                    Inst::StructInit(_, struct_ty) => {
                        if struct_ty.path.to_string().contains("Pair") {
                            saw_pair_literal = true;
                        }
                    }
                    Inst::SetLocal(_, value) => {
                        if let Value::Call(call) = value {
                            if call.fn_ref.is_some() {
                                saw_closure_call = true;
                                assert_eq!(
                                    call.args.len(),
                                    3,
                                    "closure call should pass env + two arguments"
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        assert!(
            saw_pair_literal,
            "expected Pair struct literal to lower through StructInit\n--- LIR Program ---\n{}",
            prog
        );
        assert!(
            saw_closure_call,
            "expected Call::new_ref instruction when invoking the lambda\n--- LIR Program ---\n{:#?}",
            prog
        );

        let closure_func = prog
            .funcs
            .iter()
            .find(|func| func.name.to_string().contains("$closure_"))
            .expect("lowering should emit a dedicated closure function");
        assert_eq!(
            closure_func.params.len(),
            3,
            "closure should accept env + two parameters"
        );
        let env_param = closure_func
            .params
            .first()
            .expect("closure function must start with env parameter");
        match &env_param.ty {
            Ty::RawPtr(inner) => assert_eq!(
                **inner,
                Ty::u8(),
                "env parameter should be backed by rawptr, got {}",
                inner
            ),
            other => panic!(
                "expected closure env parameter to be a rawptr[u8], got {}",
                other
            ),
        }
    }

    #[test]
    fn generates_index_operator() {
        let src = r#"
trait Index['a, 'el, 'idx] {
    fn get(self: *'a, idx: 'idx) -> 'el?
}

struct Box { v: u32 }

impl Index[Box, u32, u32] {
    fn get(self: *Box, idx: u32) -> u32? {
        nil
    }
}

pub fn main() -> u32 {
    b = Box { v: 1u32 }
    x = b[0u32]
    0u32
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        generate(&db, false).expect("lir generation should succeed");
    }

    #[test]
    fn generates_index_assignment() {
        let src = r#"
trait Index['a, 'el, 'idx] {
    fn get(self: *'a, idx: 'idx) -> 'el?
    fn set(self: *'a, idx: 'idx, el: 'el) -> 'el?
}

struct Box { v: u32 }

impl Index[Box, u32, u32] {
    fn get(self: *Box, idx: u32) -> u32? { nil }
    fn set(self: *Box, idx: u32, el: u32) -> u32? { nil }
}

pub fn main() -> u32 {
    b = Box { v: 1u32 }
    b[0u32] = 2u32
    0u32
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        generate(&db, false).expect("lir generation should succeed");
    }

    #[test]
    fn generates_field_assignment() {
        let src = r#"
struct Pair { x: u32, y: u32 }

pub fn main() -> u32 {
    p = Pair { x: 1u32, y: 2u32 }
    p.x = 3u32
    0u32
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        generate(&db, false).expect("lir generation should succeed");
    }

    #[test]
    fn generates_while_break_exits_loop() {
        let src = r#"
pub fn main() -> u32 {
    mut x = 0u32
    while true {
        x = 1u32
        break
    }
    x = 2u32
    x
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        let loop_header = main_func
            .blocks
            .iter()
            .find(|block| block.is_loop_header())
            .expect("expected at least one loop header block");
        let cond_label = loop_header.label();

        let Some(Inst::If(loop_if)) = loop_header.last() else {
            panic!(
                "expected loop header to end with Inst::If\n--- LIR Program ---\n{}",
                prog
            );
        };
        let break_label = loop_if.else_label;

        let break_block = main_func
            .blocks
            .iter()
            .find(|block| block.label() == break_label)
            .expect("expected loop break target block to exist");
        let Some(Inst::Goto(after_label)) = break_block.last().cloned() else {
            panic!(
                "expected break target block to end with Inst::Goto\n--- LIR Program ---\n{}",
                prog
            );
        };

        let after_block = main_func
            .blocks
            .iter()
            .find(|block| block.label() == after_label)
            .expect("expected post-loop block to exist");
        assert!(
            after_block
                .markers()
                .iter()
                .any(|marker| matches!(marker, ControlMarker::End(label) if *label == cond_label)),
            "expected post-loop block to be marked as End({}), got markers={:?}\n--- LIR Program ---\n{}",
            cond_label,
            after_block.markers(),
            prog
        );
    }

    #[test]
    fn generates_for_loop_calls_iter_next() {
        let src = r#"
trait Iter['it, 'el] {
    fn next(self: *'it) -> 'el?
}

trait Iterable['c, 'it, 'el] {
    fn iter(self: *'c) -> 'it
}

struct Counter { start: u32 }
struct CounterIter { done: bool }

impl Iterable[Counter, CounterIter, u32] {
    fn iter(self: *Counter) -> CounterIter {
        CounterIter { done: false }
    }
}

impl Iter[CounterIter, u32] {
    fn next(self: *CounterIter) -> u32? { nil }
}

pub fn main() -> u32 {
    c = Counter { start: 0u32 }
    for x in c {
        y = x
    }
    0u32
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        let mut saw_iter = false;
        let mut saw_next = false;

        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::SetLocal(_, value) = inst {
                    if let Value::Call(call) = value {
                        let name = call.fn_name.to_string();
                        if name.contains("Iterable::iter") {
                            saw_iter = true;
                        }
                        if name.contains("Iter::next") {
                            saw_next = true;
                        }
                    }
                }
            }
        }

        assert!(
            saw_iter,
            "expected `for` lowering to call Iterable::iter\n--- LIR Program ---\n{}",
            prog
        );
        assert!(
            saw_next,
            "expected `for` lowering to call Iter::next\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_unary_operator() {
        let src = r#"
@intrinsic extern fn bool_not(a: bool) -> bool

trait Not['a] {
    fn !(a: 'a) -> 'a
}

impl Not[bool] {
    fn !(a: bool) -> bool => bool_not(a)
}

pub fn main() -> bool {
    x = true
    !x
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        let mut saw_not_call = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::SetLocal(_, value) = inst {
                    if let Value::Call(call) = value {
                        let name = call.fn_name.to_string();
                        if name.contains("Not::!") {
                            saw_not_call = true;
                        }
                    }
                }
            }
        }

        assert!(
            saw_not_call,
            "expected unary `!` to call Not::!\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_method_call_on_struct() {
        let src = r#"
struct Counter { value: u32 }

impl object Counter {
    fn get(self: *Counter) -> u32 {
        self.value
    }
}

pub fn main() -> u32 {
    c = Counter { value: 42u32 }
    c.get()
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        // Verify the Counter::get method was generated
        let get_func = prog
            .funcs
            .iter()
            .find(|f| f.name.to_string().contains("Counter::get"));
        assert!(
            get_func.is_some(),
            "expected Counter::get function to be generated\n--- LIR Program ---\n{}",
            prog
        );

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check that we have a call to the get method (mangled name contains "get")
        let mut saw_method_call = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::SetLocal(_, value) = inst {
                    if let Value::Call(call) = value {
                        let name = call.fn_name.to_string();
                        // The call is mangled but includes "get" with type params
                        if name.contains("get") {
                            saw_method_call = true;
                        }
                    }
                }
            }
        }

        assert!(
            saw_method_call,
            "expected method call to get\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_if_else_expression() {
        let src = r#"
pub fn main() -> u32 {
    x = 1u32
    y = if true { x } else { 0u32 }
    y
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check that we have a conditional branch (Inst::If)
        let mut saw_if = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if matches!(inst, Inst::If(_)) {
                    saw_if = true;
                }
            }
        }

        assert!(
            saw_if,
            "expected if-else to generate Inst::If\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_closure_capturing_variable() {
        let src = r#"
@intrinsic extern fn u32_add(a: u32, b: u32) -> u32

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

impl Add[u32, u32, u32] {
    fn +(lhs: u32, rhs: u32) -> u32 => u32_add(lhs, rhs)
}

pub fn main() -> u32 {
    captured = 10u32
    f = (x) => x + captured
    f(5u32)
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        // Find the closure function
        let closure_func = prog
            .funcs
            .iter()
            .find(|func| func.name.to_string().contains("$closure_"));

        assert!(
            closure_func.is_some(),
            "expected closure function to be generated\n--- LIR Program ---\n{}",
            prog
        );

        // Check that we have a closure env struct type
        let has_closure_env = prog
            .struct_types
            .keys()
            .any(|path| path.to_string().contains("__closure_env_"));

        assert!(
            has_closure_env,
            "expected closure env struct type\n--- Struct Types ---\n{:?}",
            prog.struct_types.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn generates_nil_value() {
        let src = r#"
pub fn main() -> u32? {
    nil
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check that we generate a StructInit for nilable
        let mut saw_nilable_init = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::StructInit(_, struct_ty) = inst {
                    if struct_ty.path.to_string().contains("nilable") {
                        saw_nilable_init = true;
                    }
                }
            }
        }

        assert!(
            saw_nilable_init,
            "expected nil to generate nilable StructInit\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_some_value() {
        let src = r#"
pub fn main() -> u32? {
    some(42u32)
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check that we generate a StructInit for nilable with is_some = true
        let mut saw_nilable_init = false;
        let mut saw_is_some_field = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                match inst {
                    Inst::StructInit(_, struct_ty) => {
                        if struct_ty.path.to_string().contains("nilable") {
                            saw_nilable_init = true;
                        }
                    }
                    Inst::SetField(set_field) => {
                        if set_field.field == "is_some" {
                            saw_is_some_field = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        assert!(
            saw_nilable_init,
            "expected some() to generate nilable StructInit\n--- LIR Program ---\n{}",
            prog
        );
        assert!(
            saw_is_some_field,
            "expected some() to set is_some field\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_nested_binary_ops() {
        let src = r#"
@intrinsic extern fn u32_add(a: u32, b: u32) -> u32
@intrinsic extern fn u32_mul(a: u32, b: u32) -> u32

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

trait Mul['a, 'b, 'c] {
    fn *(lhs: 'a, rhs: 'b) -> 'c
}

impl Add[u32, u32, u32] {
    fn +(lhs: u32, rhs: u32) -> u32 => u32_add(lhs, rhs)
}

impl Mul[u32, u32, u32] {
    fn *(lhs: u32, rhs: u32) -> u32 => u32_mul(lhs, rhs)
}

pub fn main() -> u32 {
    a = 1u32
    b = 2u32
    c = 3u32
    a + b * c
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        let mut saw_add = false;
        let mut saw_mul = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::SetLocal(_, value) = inst {
                    if let Value::Call(call) = value {
                        let name = call.fn_name.to_string();
                        if name.contains("Add::+") {
                            saw_add = true;
                        }
                        if name.contains("Mul::*") {
                            saw_mul = true;
                        }
                    }
                }
            }
        }

        assert!(
            saw_add && saw_mul,
            "expected nested binary ops to call both Add::+ and Mul::*\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_float_literal() {
        let src = r#"
pub fn main() -> f64 {
    3.14
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check that we have a float constant
        let mut saw_float = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::SetLocal(_, value) = inst {
                    if let Value::Atom(atom) = value {
                        if matches!(atom, ray_lir::Atom::FloatConst(..)) {
                            saw_float = true;
                        }
                    }
                }
            }
        }

        assert!(
            saw_float,
            "expected float literal to generate FloatConst\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_string_literal() {
        let src = r#"
struct string {
    raw_ptr: *u8
    len: uint
    char_len: uint
}

pub fn main() -> string {
    "hello"
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        // Check that we have data for the string
        assert!(
            !prog.data.is_empty(),
            "expected string literal to add data entry\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_tuple() {
        let src = r#"
pub fn main() -> (u32, bool) {
    (42u32, true)
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check that we generate Insert instructions for tuple elements
        let mut saw_insert = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if matches!(inst, Inst::Insert(_)) {
                    saw_insert = true;
                }
            }
        }

        assert!(
            saw_insert,
            "expected tuple to generate Insert instructions\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_range_expression() {
        // Test the Expr::Range code path using arrow function syntax.
        // Range expressions use `..<` for exclusive ranges and `..=` for inclusive.
        let src = r#"
struct range['a] {
    start: 'a
    end: 'a
    inclusive: bool
}

fn make_range(a: u32, b: u32) -> range[u32] => a..<b

pub fn main() -> bool {
    r = make_range(1u32, 10u32)
    r.inclusive
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        // Find the make_range function which contains the range expression
        let range_func = prog
            .funcs
            .iter()
            .find(|f| f.name.to_string().contains("make_range"))
            .expect("expected make_range function to be generated");

        // Check that we set start, end, and inclusive fields for range
        let mut saw_start = false;
        let mut saw_end = false;
        let mut saw_inclusive = false;
        for block in &range_func.blocks {
            for inst in block.iter() {
                if let Inst::SetField(sf) = inst {
                    match sf.field.as_str() {
                        "start" => saw_start = true,
                        "end" => saw_end = true,
                        "inclusive" => saw_inclusive = true,
                        _ => {}
                    }
                }
            }
        }

        assert!(
            saw_start && saw_end && saw_inclusive,
            "expected range expression to set start, end, and inclusive fields\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_ref_and_deref() {
        let src = r#"
pub fn main() -> u32 {
    x = 42u32
    p = &x
    *p
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check for Lea (address-of) and Load (dereference)
        let mut saw_lea = false;
        let mut saw_load = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::SetLocal(_, value) = inst {
                    match value {
                        Value::Lea(_) => saw_lea = true,
                        Value::Load(_) => saw_load = true,
                        _ => {}
                    }
                }
            }
        }

        assert!(
            saw_lea,
            "expected &x to generate Lea\n--- LIR Program ---\n{}",
            prog
        );
        assert!(
            saw_load,
            "expected *p to generate Load\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_list_literal() {
        let src = r#"
struct list['el] {
    values: *'el,
    len: uint,
    capacity: uint
}

pub fn main() -> list[u32] {
    [1u32, 2u32, 3u32]
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check for Malloc (for values array) and StructInit for list
        let mut saw_malloc = false;
        let mut saw_list_init = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                match inst {
                    Inst::SetLocal(_, Value::Malloc(_)) => saw_malloc = true,
                    Inst::StructInit(_, struct_ty) => {
                        if struct_ty.path.to_string().contains("list") {
                            saw_list_init = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        assert!(
            saw_malloc,
            "expected list literal to allocate memory for values\n--- LIR Program ---\n{}",
            prog
        );
        assert!(
            saw_list_init,
            "expected list literal to generate StructInit for list\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_boxed_expression() {
        let src = r#"
pub fn main() -> *u32 {
    box 42u32
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check for Malloc (heap allocation) and Store (storing value)
        let mut saw_malloc = false;
        let mut saw_store = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                match inst {
                    Inst::SetLocal(_, Value::Malloc(_)) => saw_malloc = true,
                    Inst::Store(_) => saw_store = true,
                    _ => {}
                }
            }
        }

        assert!(
            saw_malloc,
            "expected `box` to allocate memory\n--- LIR Program ---\n{}",
            prog
        );
        assert!(
            saw_store,
            "expected `box` to store value into allocated memory\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_return_statement() {
        let src = r#"
pub fn main() -> u32 {
    if true {
        return 1u32
    }
    2u32
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Count number of Ret instructions (should have at least 2 - one from return and one from implicit)
        let ret_count = main_func
            .blocks
            .iter()
            .flat_map(|b| b.iter())
            .filter(|inst| matches!(inst, Inst::Return(_)))
            .count();

        assert!(
            ret_count >= 2,
            "expected at least 2 Ret instructions (explicit return + implicit)\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_continue_statement() {
        let src = r#"
pub fn main() -> u32 {
    mut x = 0u32
    while true {
        x = 1u32
        continue
    }
    x
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check that we have a loop header
        let has_loop = main_func.blocks.iter().any(|block| block.is_loop_header());

        assert!(
            has_loop,
            "expected continue to be in a loop\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_if_some_pattern() {
        let src = r#"
fn get_value() -> u32? {
    some(42u32)
}

pub fn main() -> u32 {
    if some(x) = get_value() {
        x
    } else {
        0u32
    }
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check that we read the is_some field (for condition) and payload field (for binding)
        let mut saw_is_some = false;
        let mut saw_payload = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::SetLocal(_, Value::GetField(gf)) = inst {
                    match gf.field.as_str() {
                        "is_some" => saw_is_some = true,
                        "payload" => saw_payload = true,
                        _ => {}
                    }
                }
            }
        }

        assert!(
            saw_is_some,
            "expected if some() to check is_some field\n--- LIR Program ---\n{}",
            prog
        );
        assert!(
            saw_payload,
            "expected if some(x) to extract payload field\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_function_as_value() {
        let src = r#"
fn add_one(x: u32) -> u32 {
    x
}

pub fn main() -> u32 {
    f = add_one
    f(1u32)
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        // Check that we have a function handle struct type and wrapper function
        let has_fn_handle = prog
            .struct_types
            .keys()
            .any(|path| path.to_string().contains("__fn_handle"));

        let has_wrapper = prog
            .funcs
            .iter()
            .any(|f| f.name.to_string().contains("$fn_handle"));

        assert!(
            has_fn_handle,
            "expected function-as-value to create __fn_handle struct type\n--- Struct Types ---\n{:?}",
            prog.struct_types.keys().collect::<Vec<_>>()
        );
        assert!(
            has_wrapper,
            "expected function-as-value to create $fn_handle wrapper\n--- Functions ---\n{:?}",
            prog.funcs.iter().map(|f| &f.name).collect::<Vec<_>>()
        );
    }

    #[test]
    fn generates_scoped_access_call_impl_object() {
        let src = r#"
struct Counter { value: u32 }

impl object Counter {
    fn create() -> Counter {
        Counter { value: 0u32 }
    }
}

pub fn main() -> Counter {
    Counter::create()
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check that we call Counter::create
        let mut saw_create_call = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::SetLocal(_, Value::Call(call)) = inst {
                    if call.fn_name.to_string().contains("create") {
                        saw_create_call = true;
                    }
                }
            }
        }

        assert!(
            saw_create_call,
            "expected Type::method() to call the method\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_scoped_access_call_trait() {
        let src = r#"
trait Factory['t] {
    fn create() -> 't
}

struct Widget { id: u32 }

impl Factory[Widget] {
    fn create() -> Widget {
        Widget { id: 1u32 }
    }
}

pub fn main() -> Widget {
    Factory[Widget]::create()
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check that we call Factory::create
        let mut saw_create_call = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::SetLocal(_, Value::Call(call)) = inst {
                    if call.fn_name.to_string().contains("create") {
                        saw_create_call = true;
                    }
                }
            }
        }

        assert!(
            saw_create_call,
            "expected Trait[Type]::method() to call the method\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_new_expression() {
        let src = r#"
pub fn main() -> *u32 {
    new(u32)
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check for Malloc instruction
        let mut saw_malloc = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if matches!(inst, Inst::SetLocal(_, Value::Malloc(_))) {
                    saw_malloc = true;
                }
            }
        }

        assert!(
            saw_malloc,
            "expected `new` to generate Malloc\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_resolved_ty_in_new_expression() {
        let src = r#"
struct A {}

pub fn main() -> *A {
    new(A)
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check for Malloc instruction
        let mut saw_malloc = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::SetLocal(_, Value::Malloc(malloc)) = inst {
                    saw_malloc = true;
                    let path = malloc.ty.mono().item_path();
                    assert!(
                        path.is_some(),
                        "expected path for malloc type: {:?}",
                        malloc
                    );
                    assert_eq!(path.unwrap().to_string(), "test::A".to_string());
                    break;
                }
            }
        }

        assert!(
            saw_malloc,
            "expected `new` to generate Malloc\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_cast_expression() {
        let src = r#"
pub fn main() -> u64 {
    x = 42u32
    x as u64
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check for Cast instruction
        let mut saw_cast = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if matches!(inst, Inst::SetLocal(_, Value::Cast(_))) {
                    saw_cast = true;
                }
            }
        }

        assert!(
            saw_cast,
            "expected `as` to generate Cast\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_for_loop_with_some_pattern() {
        let src = r#"
trait Iter['it, 'el] {
    fn next(self: *'it) -> 'el?
}

trait Iterable['c, 'it, 'el] {
    fn iter(self: *'c) -> 'it
}

struct MaybeIter { done: bool }

impl Iterable[MaybeIter, MaybeIter, u32?] {
    fn iter(self: *MaybeIter) -> MaybeIter {
        MaybeIter { done: false }
    }
}

impl Iter[MaybeIter, u32?] {
    fn next(self: *MaybeIter) -> (u32?)? {
        nil
    }
}

pub fn main() -> u32 {
    m = MaybeIter { done: false }
    for some(x) in m {
        y = x
    }
    0u32
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check that we have a loop
        let has_loop = main_func.blocks.iter().any(|b| b.is_loop_header());

        assert!(
            has_loop,
            "expected for loop with some pattern\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_deref_assignment() {
        // This test exercises assignment through a dereferenced pointer: *p = value
        let src = r#"
pub fn main() -> u32 {
    x = 42u32
    p = &x
    *p = 100u32
    x
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Check for Store instruction (writing through pointer)
        let mut saw_store = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if matches!(inst, Inst::Store(_)) {
                    saw_store = true;
                }
            }
        }

        assert!(
            saw_store,
            "expected *p = value to generate Store\n--- LIR Program ---\n{}",
            prog
        );
    }

    /// Regression test: compound assignment desugaring (`i += 1` → `i = i + 1`)
    /// must produce correct LIR. The desugared BinOp expression needs a valid
    /// call_resolution so call_from_op can look up the operator implementation.
    #[test]
    fn generates_compound_assignment_in_while_loop() {
        let src = r#"
@intrinsic extern fn u32_add(a: u32, b: u32) -> u32
@intrinsic extern fn u32_lt(a: u32, b: u32) -> bool

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

trait Lt['a, 'b] {
    fn <(a: 'a, b: 'b) -> bool
}

impl Add[u32, u32, u32] {
    fn +(lhs: u32, rhs: u32) -> u32 => u32_add(lhs, rhs)
}

impl Lt[u32, u32] {
    fn <(a: u32, b: u32) -> bool => u32_lt(a, b)
}

pub fn main() -> u32 {
    mut i = 0u32
    while i < 10u32 {
        i += 1u32
    }
    i
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false)
            .expect("lir generation should succeed for compound assignment in while loop");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let _main_func = &prog.funcs[user_main_idx];
    }

    /// Regression test: compound assignment desugaring (`i += 1` → `i = i + 1`)
    /// across multiple files. The operator trait is defined in one file and the
    /// function using `+=` is in another file.
    #[test]
    fn generates_compound_assignment_cross_file() {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();

        let module_path = ModulePath::from("test");
        let entry_file = workspace.add_file(FilePath::from("test/entry.ray"), module_path.clone());
        let ops_file = workspace.add_file(FilePath::from("test/ops.ray"), module_path.clone());
        workspace.entry = Some(entry_file);

        db.set_input::<WorkspaceSnapshot>((), workspace);
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: true });
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());

        FileSource::new(
            &db,
            ops_file,
            r#"
@intrinsic extern fn u32_add(a: u32, b: u32) -> u32
@intrinsic extern fn u32_lt(a: u32, b: u32) -> bool

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

trait Lt['a, 'b] {
    fn <(a: 'a, b: 'b) -> bool
}

impl Add[u32, u32, u32] {
    fn +(lhs: u32, rhs: u32) -> u32 => u32_add(lhs, rhs)
}

impl Lt[u32, u32] {
    fn <(a: u32, b: u32) -> bool => u32_lt(a, b)
}
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            ops_file,
            FilePath::from("test/ops.ray"),
            module_path.clone(),
        );

        FileSource::new(
            &db,
            entry_file,
            r#"
pub fn main() -> u32 {
    mut i = 0u32
    while i < 10u32 {
        i += 1u32
    }
    i
}
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            entry_file,
            FilePath::from("test/entry.ray"),
            module_path.clone(),
        );

        let prog = generate(&db, false)
            .expect("lir generation should succeed for compound assignment across files");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let _main_func = &prog.funcs[user_main_idx];
    }

    /// Regression test: when a workspace has multiple files, LIR generation
    /// must look up name resolutions using the node's owning file, not the
    /// entry file. Otherwise, function calls in non-entry files panic with
    /// "missing binding for name expr".
    #[test]
    fn generates_cross_file_function_call() {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();

        let module_path = ModulePath::from("test");
        let entry_file = workspace.add_file(FilePath::from("test/entry.ray"), module_path.clone());
        let helper_file =
            workspace.add_file(FilePath::from("test/helper.ray"), module_path.clone());
        workspace.entry = Some(entry_file);

        db.set_input::<WorkspaceSnapshot>((), workspace);
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: true });
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());

        FileSource::new(&db, entry_file, "pub fn main() -> u32 { 0u32 }".to_string());
        FileMetadata::new(
            &db,
            entry_file,
            FilePath::from("test/entry.ray"),
            module_path.clone(),
        );
        FileSource::new(
            &db,
            helper_file,
            r#"
fn helper() -> u32 { 42u32 }
fn caller() -> u32 { helper() }
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            helper_file,
            FilePath::from("test/helper.ray"),
            module_path.clone(),
        );

        let prog = generate(&db, false)
            .expect("lir generation should succeed for multi-file workspace with cross-file calls");

        // Verify both helper and caller functions were generated
        let has_helper = prog
            .funcs
            .iter()
            .any(|f| f.name.to_string().contains("helper"));
        let has_caller = prog
            .funcs
            .iter()
            .any(|f| f.name.to_string().contains("caller"));
        assert!(
            has_helper,
            "expected helper function to be generated\n--- LIR Program ---\n{}",
            prog
        );
        assert!(
            has_caller,
            "expected caller function to be generated\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_generic_operator_call_from_bounds() {
        let (db, _files) = setup_test_workspace_with_files(vec![
            TestWorkspaceFile {
                filepath: "mod.ray".to_string(),
                module_path: "test".to_string(),
                source: r#"
                fn invert(a: 'a) -> 'a where Neg['a, 'a] {
                    -a
                }
            "#
                .to_string(),
            },
            TestWorkspaceFile {
                filepath: "ops.ray".to_string(),
                module_path: "test".to_string(),
                source: r#"
                trait Sub['a, 'b, 'c] { fn -(self: 'a, other: 'b) -> 'c }
                trait Neg['a, 'b] { fn -(self: 'a) -> 'b }
            "#
                .to_string(),
            },
        ]);

        let _prog = generate(&db, true).expect("lir generation should succeed");
    }

    #[test]
    fn generates_nil_coalesce_with_default_value() {
        let src = r#"
fn get_value() -> u32? {
    some(42u32)
}

pub fn main() -> u32 {
    get_value() else 0u32
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // NilCoalesce should branch on `is_some` and extract `payload`
        let mut saw_if = false;
        let mut saw_is_some = false;
        let mut saw_payload = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if matches!(inst, Inst::If(_)) {
                    saw_if = true;
                }
                if let Inst::SetLocal(_, Value::GetField(gf)) = inst {
                    match gf.field.as_str() {
                        "is_some" => saw_is_some = true,
                        "payload" => saw_payload = true,
                        _ => {}
                    }
                }
            }
        }

        assert!(
            saw_if,
            "expected nil coalesce to generate Inst::If\n--- LIR Program ---\n{}",
            prog
        );
        assert!(
            saw_is_some,
            "expected nil coalesce to check is_some field\n--- LIR Program ---\n{}",
            prog
        );
        assert!(
            saw_payload,
            "expected nil coalesce to extract payload field\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_nil_coalesce_with_return() {
        let src = r#"
fn get_value() -> u32? {
    some(42u32)
}

pub fn main() -> u32 {
    get_value() else return 0u32
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // The else-branch should contain a Ret instruction
        let mut saw_if = false;
        let mut saw_ret_count = 0;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if matches!(inst, Inst::If(_)) {
                    saw_if = true;
                }
                if matches!(inst, Inst::Return(_)) {
                    saw_ret_count += 1;
                }
            }
        }

        assert!(
            saw_if,
            "expected nil coalesce to generate Inst::If\n--- LIR Program ---\n{}",
            prog
        );
        // At least 2 returns: the `return 0u32` in else-branch and the implicit main return
        assert!(
            saw_ret_count >= 2,
            "expected at least 2 Ret instructions (else return + implicit), got {}\n--- LIR Program ---\n{}",
            saw_ret_count,
            prog
        );
    }

    #[test]
    fn generates_nil_coalesce_assigned_to_variable() {
        let src = r#"
fn get_value() -> u32? {
    some(42u32)
}

pub fn main() -> u32 {
    x = get_value() else 99u32
    x
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // Should have an if-branch (from nil coalesce) and both is_some + payload field access
        let mut saw_if = false;
        let mut saw_is_some = false;
        let mut saw_payload = false;
        for block in &main_func.blocks {
            for inst in block.iter() {
                if matches!(inst, Inst::If(_)) {
                    saw_if = true;
                }
                if let Inst::SetLocal(_, Value::GetField(gf)) = inst {
                    match gf.field.as_str() {
                        "is_some" => saw_is_some = true,
                        "payload" => saw_payload = true,
                        _ => {}
                    }
                }
            }
        }

        assert!(
            saw_if && saw_is_some && saw_payload,
            "expected nil coalesce in assignment to generate if/is_some/payload\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_fstring_with_interpolation() {
        let src = r#"
struct string {
    raw_ptr: *u8
    len: uint
    char_len: uint
}

@intrinsic extern fn str_concat(a: string, b: string) -> string

trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

impl ToStr[string] {
    fn to_str(self: string) -> string { self }
}

impl Add[string, string, string] {
    fn +(lhs: string, rhs: string) -> string => str_concat(lhs, rhs)
}

pub fn main() -> string {
    name = "world"
    f"hello {name}"
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        let mut saw_to_str = false;
        let mut saw_add = false;

        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::SetLocal(_, Value::Call(call)) = inst {
                    let name = call.fn_name.to_string();
                    if name.contains("ToStr::to_str") {
                        saw_to_str = true;
                    }
                    if name.contains("Add::+") {
                        saw_add = true;
                    }
                }
            }
        }

        assert!(
            saw_to_str,
            "expected f-string to call ToStr::to_str\n--- LIR Program ---\n{}",
            prog
        );
        assert!(
            saw_add,
            "expected f-string to call Add::+ for concatenation\n--- LIR Program ---\n{}",
            prog
        );
    }

    #[test]
    fn generates_fstring_literal_only_no_trait_calls() {
        // A literal-only f-string needs neither ToStr nor Add in scope
        let src = r#"
struct string {
    raw_ptr: *u8
    len: uint
    char_len: uint
}

pub fn main() -> string {
    f"hello"
}
"#;

        let (db, _file_id) = setup_test_workspace(src);
        let prog = generate(&db, false).expect("lir generation should succeed");

        let user_main_idx: usize = prog
            .user_main_idx
            .try_into()
            .expect("user main index should be set");
        let main_func = &prog.funcs[user_main_idx];

        // A literal-only f-string should NOT generate any trait calls
        for block in &main_func.blocks {
            for inst in block.iter() {
                if let Inst::SetLocal(_, Value::Call(call)) = inst {
                    let name = call.fn_name.to_string();
                    assert!(
                        !name.contains("ToStr::to_str") && !name.contains("Add::+"),
                        "literal-only f-string should not call trait methods, but found: {}\n--- LIR Program ---\n{}",
                        name,
                        prog
                    );
                }
            }
        }

        // Should still produce string data
        assert!(
            !prog.data.is_empty(),
            "expected f-string literal to produce data entry\n--- LIR Program ---\n{}",
            prog
        );
    }
}

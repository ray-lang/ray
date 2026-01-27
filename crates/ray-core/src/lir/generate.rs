use std::{cell::RefCell, collections::HashMap, ops::Deref, rc::Rc};

use ray_shared::{
    collections::namecontext::NameContext,
    node_id::NodeId,
    pathlib::{ItemPath, ModulePath, Path},
    span::Source,
    ty::Ty,
};
use ray_typing::{
    BindingKind, BindingRecord, NodeBinding,
    binding_groups::BindingId,
    tyctx::{CallResolution, TyCtx},
    types::{ImplKind, NominalKind, ReceiverMode, StructTy, Subst, Substitutable, TyScheme},
    unify::match_ty,
};

use crate::{
    ast::{
        self, Assign, BinOp, Call, Closure, CurlyElement, Decl, Expr, Literal, Modifier, Module,
        Node, Pattern, PrefixOp, RangeLimits, UnaryOp, token::IntegerBase,
    },
    errors::RayResult,
    lir,
    passes::{
        binding::BindingPassOutput,
        closure::{ClosurePassOutput, LegacyClosureInfo},
    },
    sema,
    sourcemap::SourceMap,
};

use super::START_FUNCTION;

fn resolve_user_main_info(module: &Module<(), Decl>, tcx: &TyCtx) -> Option<(Path, TyScheme)> {
    let expected = module.path.append("main");
    module.decls.iter().find_map(|decl| match &decl.value {
        Decl::Func(func) => {
            let func_path = func.sig.path.value.with_names_only();
            if func_path != expected {
                return None;
            }
            let fn_ty = tcx.instantiate_scheme(tcx.ty_of(decl.id));
            let fn_name = if fn_ty.is_polymorphic() {
                func.sig.path.value.clone()
            } else {
                sema::fn_name(&func.sig.path.value, &fn_ty)
            };
            Some((fn_name, fn_ty))
        }
        _ => None,
    })
}

impl lir::Program {
    pub fn generate(
        module: &Module<(), Decl>,
        tcx: &TyCtx,
        ncx: &NameContext,
        srcmap: &SourceMap,
        bindings: &BindingPassOutput,
        closure_info: &ClosurePassOutput,
        libs: Vec<lir::Program>,
    ) -> RayResult<lir::Program> {
        let path = module.path.clone();
        let user_main_info = resolve_user_main_info(module, tcx);
        let prog = Rc::new(RefCell::new(lir::Program::new(path)));
        let mut ctx = GenCtx::new(Rc::clone(&prog), srcmap, ncx, bindings, closure_info);
        module.decls.lir_gen(&mut ctx, tcx)?;

        let (module_main_path, user_main_base_path) = {
            let prog_ref = prog.borrow();
            (
                prog_ref.main_path(),
                prog_ref.module_path.clone().append("main"),
            )
        };

        let has_module_main = {
            let prog_ref = prog.borrow();
            prog_ref.funcs.iter().any(|f| f.name == module_main_path)
        };

        if !has_module_main {
            ctx.with_builder(lir::Builder::new());
            ctx.with_new_block(|ctx| {
                ctx.ret(lir::Value::Empty);
            });

            let builder = ctx.builder.take().unwrap();
            let (params, locals, blocks, symbols, cfg) = builder.done();
            let mut module_main_fn = Node::new(lir::Func::new(
                module_main_path.clone(),
                TyScheme::from_mono(Ty::Func(vec![], Box::new(Ty::unit()))),
                vec![],
                symbols,
                cfg,
            ));
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

        let start_idx = if !module.is_lib {
            let mut main_symbols = lir::SymbolSet::new();
            log::debug!("module main path: {}", module_main_path);
            if let Some(user_main_resolved_path) = &user_main_resolved_path {
                log::debug!("user main path (resolved): {}", user_main_resolved_path);
            } else {
                log::debug!("user main path (resolved): None");
            }

            ctx.with_builder(lir::Builder::new());
            ctx.with_new_block(|ctx| {
                // call all the main functions from the libs first
                let mut main_funcs = libs.iter().map(|l| l.main_path()).collect::<Vec<_>>();

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
            let mut start_fn = Node::new(lir::Func::new(
                START_FUNCTION.into(),
                TyScheme::from_mono(Ty::Func(vec![], Box::new(Ty::unit()))),
                vec![],
                symbols,
                cfg,
            ));
            start_fn.params = params;
            start_fn.locals = locals;
            start_fn.blocks = blocks;
            start_fn.symbols.extend(main_symbols);
            ctx.new_func(start_fn) as i64
        } else {
            -1
        };

        let mut synthetic_structs = HashMap::new();
        for struct_ty in ctx
            .closure_env_types
            .values()
            .chain(ctx.closure_value_types.values())
            .chain(ctx.fn_handle_types.values())
        {
            synthetic_structs.insert(struct_ty.path.clone(), struct_ty.clone());
        }

        drop(ctx);

        // take the prog out of the pointer
        let mut prog = Rc::try_unwrap(prog).unwrap().into_inner();
        prog.start_idx = start_idx;
        prog.resolved_user_main = user_main_resolved_path.clone();
        prog.synthetic_structs = synthetic_structs;
        prog.impls_by_trait = tcx
            .global_env
            .impls_by_trait
            .iter()
            .map(|(s, indices)| {
                let impls = indices
                    .iter()
                    .flat_map(|idx| tcx.global_env.resolve_impl_from_index(idx))
                    .cloned()
                    .collect();
                (s.clone(), impls)
            })
            .collect();
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

    pub fn monomorphize(&mut self) {
        let mut mr = sema::Monomorphizer::new(self);
        let funcs = mr.monomorphize();

        let mono_fn_externs = mr.mono_fn_externs();
        for (poly_fn, mono_fns) in mono_fn_externs {
            let poly_idx = *self.extern_map.get(&poly_fn).unwrap();
            for (mono_fn, mono_ty) in mono_fns {
                let mut mono_ext = self.externs[poly_idx].clone();
                mono_ext.name = mono_fn.clone();
                mono_ext.ty = TyScheme::from_mono(mono_ty);
                self.extern_map.insert(mono_fn, self.externs.len());
                self.externs.push(mono_ext);
            }
        }

        // remove the polymorphic functions
        let module_main_path = self.main_path();
        let user_main_base_path = self.module_path.clone().append("main");
        let resolved_user_main = self.resolved_user_main.clone();
        let mut i = 0;
        while i < self.funcs.len() {
            let f = &self.funcs[i];
            if f.name == START_FUNCTION {
                self.start_idx = i as i64;
            } else if let Some(resolved) = &resolved_user_main {
                if f.name == *resolved {
                    self.user_main_idx = i as i64;
                } else if f.name == module_main_path {
                    self.module_main_idx = i as i64;
                }
            } else if f.name.starts_with(&user_main_base_path) {
                self.user_main_idx = i as i64;
            } else if f.name == module_main_path {
                self.module_main_idx = i as i64;
            }

            if f.ty.is_polymorphic() {
                self.funcs.remove(i);
            } else {
                i += 1;
            }
        }

        // add the new monomorphized functions
        self.funcs.extend(funcs);
    }
}

pub trait LirGen<T> {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>, tcx: &TyCtx) -> RayResult<T>;
}

impl<T, U> LirGen<Vec<U>> for Vec<T>
where
    T: LirGen<U>,
{
    fn lir_gen(&self, ctx: &mut GenCtx<'_>, tcx: &TyCtx) -> RayResult<Vec<U>> {
        self.iter()
            .map(|t| t.lir_gen(ctx, tcx))
            .collect::<RayResult<Vec<_>>>()
    }
}

#[derive(Clone, Debug)]
pub struct GenCtx<'a> {
    prog: Rc<RefCell<lir::Program>>,
    builder: Option<lir::Builder>,
    data_idx: HashMap<Vec<u8>, usize>,
    global_idx: HashMap<String, usize>,
    pub(crate) srcmap: &'a SourceMap,
    ncx: &'a NameContext,
    bindings: &'a BindingPassOutput,
    closure_info: &'a ClosurePassOutput,
    closure_map: HashMap<NodeId, usize>,
    binding_nodes: HashMap<BindingId, NodeId>,
    closure_env_types: HashMap<NodeId, StructTy>,
    closure_value_types: HashMap<NodeId, StructTy>,
    closure_fn_types: HashMap<NodeId, TyScheme>,
    closure_funcs: HashMap<NodeId, Path>,
    fn_handle_types: HashMap<(Vec<Ty>, Ty), StructTy>,
    fn_handle_path_types: HashMap<ItemPath, StructTy>,
    fn_handle_wrappers: HashMap<(Path, Vec<Ty>, Ty), Path>,
}

impl<'a> std::ops::Deref for GenCtx<'a> {
    type Target = lir::Builder;

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
        prog: Rc<RefCell<lir::Program>>,
        srcmap: &'a SourceMap,
        ncx: &'a NameContext,
        bindings: &'a BindingPassOutput,
        closure_info: &'a ClosurePassOutput,
    ) -> GenCtx<'a> {
        let closure_map = closure_info
            .closures
            .iter()
            .enumerate()
            .map(|(idx, info)| (info.closure_expr, idx))
            .collect();
        let mut binding_nodes = HashMap::new();
        for (node_id, binding) in bindings.node_bindings.iter() {
            if let NodeBinding::Def(binding) = binding {
                binding_nodes.entry(*binding).or_insert(*node_id);
            }
        }
        GenCtx {
            prog,
            builder: None,
            data_idx: HashMap::new(),
            global_idx: HashMap::new(),
            srcmap,
            ncx,
            bindings,
            closure_info,
            closure_map,
            binding_nodes,
            closure_env_types: HashMap::new(),
            closure_value_types: HashMap::new(),
            closure_fn_types: HashMap::new(),
            closure_funcs: HashMap::new(),
            fn_handle_types: HashMap::new(),
            fn_handle_path_types: HashMap::new(),
            fn_handle_wrappers: HashMap::new(),
        }
    }

    fn ty_of(&mut self, tcx: &TyCtx, id: NodeId) -> TyScheme {
        let scheme = tcx.ty_of(id);
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

    fn with_builder(&mut self, builder: lir::Builder) -> Option<lir::Builder> {
        self.builder.replace(builder)
    }

    fn path(&self) -> Path {
        self.prog.borrow().module_path.clone()
    }

    fn add_sym(&mut self, sym: Path) {
        self.builder.as_mut().unwrap().symbols.insert(sym);
    }

    fn new_func(&mut self, func: Node<lir::Func>) -> usize {
        let mut prog = self.prog.borrow_mut();
        let idx = prog.funcs.len();
        if func.ty.is_polymorphic() {
            log::debug!("adding function to poly_fn_map: {}", func.name);
            prog.poly_fn_map.insert(func.name.clone(), idx);
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
        let path = prog.module_path.clone();
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
        let path = prog.module_path.clone();
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
        _operator_id: NodeId,
        _args: &[&Node<Expr>],
        _tcx: &TyCtx,
    ) -> RayResult<GenResult> {
        todo!("FIXME: this uses legacy code that needs to change")

        // let resolved = tcx
        //     .call_resolution(operator_id)
        //     .unwrap_or_else(|| panic!("missing call resolution for operator {:?}", operator_id));

        // let mut call_args: Vec<lir::Variable> = Vec::with_capacity(args.len());
        // for arg in args {
        //     let arg_ty = tcx.ty_of(arg.id);
        //     let arg_val = arg.lir_gen(self, tcx)?;
        //     call_args.push(self.value_to_local_or_unit(arg_val, arg_ty));
        // }

        // let fn_name = if self.is_extern(&resolved.base_fqn) {
        //     self.extern_link_name(&resolved.base_fqn)
        //         .unwrap_or_else(|| resolved.base_fqn.clone())
        // } else {
        //     sema::fn_name(&resolved.base_fqn, &resolved.callee_ty)
        // };

        // self.add_sym(fn_name.clone());
        // Ok(lir::Call::new(
        //     fn_name,
        //     call_args,
        //     resolved.callee_ty.clone(),
        //     Some(resolved.poly_callee_ty.clone()),
        // )
        // .into())
    }

    #[allow(dead_code)]
    fn closure_info(&self, node_id: NodeId) -> Option<&LegacyClosureInfo> {
        let idx = self.closure_map.get(&node_id)?;
        self.closure_info.closures.get(*idx)
    }

    fn binding_record(&self, binding: BindingId) -> Option<&BindingRecord> {
        self.bindings.binding_records.get(&binding)
    }

    fn binding_for_node(&self, node_id: NodeId) -> Option<BindingId> {
        self.bindings
            .node_bindings
            .get(&node_id)
            .copied()
            .map(|b| b.binding())
    }

    fn debug_name_for_binding(&self, binding: BindingId) -> String {
        self.binding_record(binding)
            .and_then(|rec| rec.path.as_ref())
            .and_then(|p| p.name())
            .unwrap_or_else(|| format!("__binding_{}", binding.0))
    }

    fn global_var_for_binding(&self, binding: BindingId) -> Option<lir::Variable> {
        let record = self.binding_record(binding)?;
        if record.parent.is_some() {
            return None;
        }
        let path = record.path.as_ref()?;
        let global = self.global_idx.get(&path.to_string())?;
        Some(lir::Variable::Global(self.path(), *global))
    }

    fn ensure_local_for_binding(
        &mut self,
        binding: BindingId,
        debug_name: String,
        ty: TyScheme,
    ) -> usize {
        self.get_var(&binding).copied().unwrap_or_else(|| {
            let idx = self.local(ty);
            self.set_var(binding, debug_name, idx);
            idx
        })
    }

    fn binding_node(&self, binding: BindingId) -> Option<NodeId> {
        self.binding_nodes.get(&binding).copied()
    }

    fn binding_record_for_path(&self, path: &Path) -> Option<&BindingRecord> {
        self.bindings
            .value_bindings
            .get(&path)
            .and_then(|binding| self.binding_record(*binding))
    }

    fn maybe_direct_function(&self, node_id: NodeId, path: &Path, tcx: &TyCtx) -> Option<TyScheme> {
        let scheme = tcx.ty_of(node_id);
        if matches!(scheme.mono(), Ty::Func(_, _))
            && self
                .binding_record_for_path(path)
                .map(|rec| matches!(rec.kind, BindingKind::Function { .. }))
                .unwrap_or(false)
        {
            return Some(scheme);
        }

        None
    }

    fn collect_closure_captures(
        &mut self,
        closure_id: NodeId,
        tcx: &TyCtx,
    ) -> Vec<lir::CaptureSlot> {
        let info = self
            .closure_info(closure_id)
            .expect("closure info missing for node");
        let captures: Vec<_> = info
            .captures
            .iter()
            .map(|binding| {
                let record = self
                    .binding_record(*binding)
                    .unwrap_or_else(|| panic!("missing binding record for {}", binding));
                let node_id = self
                    .binding_node(*binding)
                    .unwrap_or_else(|| panic!("missing node for binding {}", binding));
                let name = record
                    .path
                    .as_ref()
                    .and_then(|p| p.name())
                    .unwrap_or_else(|| format!("__capture_{}", binding.0));
                (*binding, name, node_id)
            })
            .collect();

        captures
            .into_iter()
            .map(|(binding, name, node_id)| {
                let ty = self.ty_of(tcx, node_id);
                let var = self
                    .get_var(&binding)
                    .copied()
                    .map(lir::Variable::Local)
                    .unwrap_or_else(|| {
                        panic!("capture `{}` is not available in the current scope", name)
                    });
                lir::CaptureSlot {
                    binding,
                    name,
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
            vec!["__fn_handle".into(), sema::fn_ty(&params, &ret).into()],
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

        let outer_builder = self.with_builder(lir::Builder::new());

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

        let mut func = Node::new(lir::Func::new(
            wrapper_path.clone(),
            wrapper_ty.clone(),
            vec![],
            symbols,
            cfg,
        ));
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
            .map(|slot| (slot.name.clone(), slot.ty.clone()))
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

    fn make_closure_path(&self, info: &LegacyClosureInfo, expr_id: NodeId) -> Path {
        if let Some(record) = self.binding_record(info.parent_binding) {
            if let Some(base) = &record.path {
                return base.append(format!("$closure_{:x}", expr_id));
            }
        }

        let mut path = self.path();
        path = path.append(format!("$closure_{:x}", expr_id));
        path
    }

    fn lower_closure(
        &mut self,
        expr: &Node<Expr>,
        closure: &Closure,
        captures: &[lir::CaptureSlot],
        env_ty: &StructTy,
        tcx: &TyCtx,
    ) -> RayResult<Path> {
        if let Some(existing) = self.closure_funcs.get(&expr.id) {
            return Ok(existing.clone());
        }

        let outer_builder = self.with_builder(lir::Builder::new());

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
                        .unwrap_or_else(|| ctx.debug_name_for_binding(binding));
                    let ty = ctx.ty_of(tcx, param.id);
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
                    field: slot.name.clone(),
                }
                .into();
                let capture_loc = ctx.local(slot.ty.clone());
                ctx.set_local(capture_loc, value);
                ctx.set_var(slot.binding, slot.name.clone(), capture_loc);
            }
        });

        let body = closure.body.as_ref();
        let body_val = if !matches!(body.value, Expr::Block(_)) {
            let (_, value) = self.with_new_block(|ctx| body.lir_gen(ctx, tcx));
            value?
        } else {
            body.lir_gen(self, tcx)?
        };

        let mut fn_ty_with_env = tcx
            .get_poly_ty(expr.id)
            .cloned()
            .unwrap_or_else(|| tcx.ty_of(expr.id));
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
                let body_ty = ctx.ty_of(tcx, body.id);
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
            .closure_info(expr.id)
            .expect("closure info missing for node");
        let fn_path = self.make_closure_path(info, expr.id);
        let mut func = Node::new(lir::Func::new(
            fn_path.clone(),
            fn_ty_with_env.clone(),
            Vec::new(),
            symbols,
            cfg,
        ));
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
                slot.name.clone(),
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
        tcx: &TyCtx,
        callee_id: NodeId,
        callee_val: lir::Value,
        call_args: Vec<lir::Variable>,
        original_poly_ty: Option<TyScheme>,
        src: &Source,
    ) -> RayResult<GenResult> {
        // callee_val has type FnHandle[A..,R]
        let handle_scheme = self.ty_of(tcx, callee_id);
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
        _resolved: &CallResolution,
        _call_args: Vec<lir::Variable>,
        _src: &Source,
    ) -> RayResult<GenResult> {
        todo!("FIXME: this uses legacy code that needs to change")

        // let fn_name = if self.is_extern(&resolved.base_fqn) {
        //     self.extern_link_name(&resolved.base_fqn)
        //         .unwrap_or_else(|| resolved.base_fqn.clone())
        // } else {
        //     sema::fn_name(&resolved.base_fqn, &resolved.callee_ty)
        // };

        // log::debug!("add sym: {}", fn_name);
        // self.add_sym(fn_name.clone());
        // let mut call = lir::Call::new(
        //     fn_name,
        //     call_args,
        //     resolved.callee_ty.clone(),
        //     Some(resolved.poly_callee_ty.clone()),
        // );
        // call.source = Some(src.clone());
        // Ok(call.into())
    }

    fn resolve_trait_method_direct_call(
        &self,
        _trait_fqn: &ItemPath,
        _method_name: &str,
        _callee_ty: TyScheme,
        _tcx: &TyCtx,
    ) -> Option<CallResolution> {
        todo!("FIXME: this uses legacy code that needs to change")

        // let trait_ty = tcx.get_trait_ty(trait_fqn)?;
        // let method_name = method_name.to_string();
        // let trait_field = trait_ty.get_field(&method_name)?;

        // let poly_callee_ty = trait_field.ty.clone();
        // let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
        //     Ok((_, subst)) => subst,
        //     Err(_) => Subst::new(),
        // };

        // let base_fqn = trait_ty.path.append(&method_name);
        // Some(CallResolution {
        //     base_fqn,
        //     poly_callee_ty,
        //     callee_ty,
        //     subst,
        // })
    }

    fn emit_trait_method_call_with_recv_local(
        &mut self,
        tcx: &TyCtx,
        trait_fqn: &ItemPath,
        method_name: &str,
        recv_loc: usize,
        recv_scheme: TyScheme,
        callee_ty: TyScheme,
        src: &Source,
    ) -> RayResult<Option<usize>> {
        let resolved = self
            .resolve_trait_method_direct_call(trait_fqn, method_name, callee_ty, tcx)
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
        let recv_mode = self.recv_mode_for_base(tcx, &resolved.base_fqn);

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
        tcx: &TyCtx,
        pat: &Node<Pattern>,
        pat_scheme: &TyScheme,
        elem_val: lir::Value,
        cond_label: usize,
        body: &Node<Expr>,
        _src: &Source,
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
                    .unwrap_or_else(|| self.debug_name_for_binding(binding));
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
                                .unwrap_or_else(|| ctx.debug_name_for_binding(binding));
                            let slot = ctx.ensure_local_for_binding(
                                binding,
                                debug_name,
                                TyScheme::from_mono(payload_mono),
                            );
                            ctx.set_local(slot, inner_val);
                        }
                        _ => todo!("lir_gen: Expr::For: complex `some(...)` pattern"),
                    }

                    let body_val = body.lir_gen(ctx, tcx)?;
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
        tcx: &TyCtx,
    ) -> Option<Ty> {
        for impl_ty in tcx.get_impls_for_trait_fqn(iterable_trait_fqn) {
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

            let mut poly_vars = std::collections::HashSet::new();
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

    fn recv_mode_for_base(&self, tcx: &TyCtx, path: &ItemPath) -> ReceiverMode {
        log::debug!("[recv_mode_for_base] func_fqn = {}", path);
        let Some(method_name) = path.item_name() else {
            log::debug!("[recv_mode_for_base] missing method name: {}", path);
            return ReceiverMode::None;
        };

        if let Some(trait_fqn) = tcx.resolve_trait_from_path(&path) {
            let Some(field) = tcx.get_trait_field(&trait_fqn, &method_name) else {
                log::debug!(
                    "[recv_mode_for_base] could not resolve trait field {} for trait: {}",
                    path,
                    trait_fqn,
                );
                return ReceiverMode::None;
            };

            log::debug!("[recv_mode_for_base] found trait field: {:?}", field);
            return field.recv_mode;
        }

        let Some(recv_fqn) = path.parent_item().filter(|path| !path.is_empty()) else {
            log::debug!(
                "[recv_mode_for_base] could not derive receiver fqn from path: {}",
                path
            );
            return ReceiverMode::None;
        };

        let Some((_, field)) = tcx.resolve_inherent_method(&recv_fqn, &method_name) else {
            log::debug!(
                "[recv_mode_for_base] could not resolve inherent method {} for recv: {}",
                method_name,
                recv_fqn
            );
            return ReceiverMode::None;
        };

        log::debug!("[recv_mode_for_base] found inherent field: {:?}", field);
        field.recv_mode
    }

    fn build_call_args(
        &mut self,
        tcx: &TyCtx,
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
                self.ty_of(tcx, expr.id),
                expr
            );

            let value = expr.lir_gen(self, tcx)?;

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
                self.ty_of(tcx, expr.id)
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
        tcx: &TyCtx,
        src: &Source,
    ) -> RayResult<()> {
        let resolved = tcx
            .call_resolution(assign_id)
            .cloned()
            .unwrap_or_else(|| panic!("missing call resolution for index assign {:#x}", assign_id));

        let param_monos = match resolved.callee_ty.mono() {
            Ty::Func(params, _) => params.clone(),
            _ => Vec::new(),
        };

        let recv_mode = self.recv_mode_for_base(tcx, &resolved.base_fqn);

        let recv_param_mono = param_monos.first();

        // Evaluate the receiver as its actual value first (e.g. `list[T]`),
        // then coerce to the receiver param (e.g. `*list[T]`) if needed.
        // If we evaluate it as the param type up-front we can accidentally
        // skip emitting `lea` and end up mutating a copy (observed in `Index::set`).
        let recv_expr_scheme = self.ty_of(tcx, container_pat.id);
        let recv_value = self.emit_pattern_value(container_pat, &recv_expr_scheme, tcx, src)?;

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

        let index_ty = self.ty_of(tcx, index_expr.id);
        let index_val = index_expr.lir_gen(self, tcx)?;
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
        tcx: &TyCtx,
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
                    .unwrap_or_else(|| self.debug_name_for_binding(binding));
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
                    .unwrap_or_else(|| self.debug_name_for_binding(binding));
                let idx = self.ensure_local_for_binding(binding, debug_name, expected_ty.clone());
                Ok(lir::Value::new(lir::Variable::Local(idx)))
            }
            Pattern::Dot(lhs, rhs) => {
                let lhs_ty = self.ty_of(tcx, lhs.id);
                let lhs_val = self.emit_pattern_value(lhs.as_ref(), &lhs_ty, tcx, src)?;
                let lhs_loc = self.get_or_set_local(lhs_val, lhs_ty.clone()).unwrap();

                Ok(lir::GetField {
                    src: lir::Variable::Local(lhs_loc),
                    field: rhs.path.name().unwrap(),
                }
                .into())
            }
            Pattern::Index(container_pat, index_expr, _) => {
                let resolved = tcx.call_resolution(pat.id).cloned().unwrap_or_else(|| {
                    panic!("missing call resolution for index pattern {:#x}", pat.id)
                });

                let param_monos = match resolved.callee_ty.mono() {
                    Ty::Func(params, _) => params.clone(),
                    _ => Vec::new(),
                };

                let recv_mode = self.recv_mode_for_base(tcx, &resolved.base_fqn);
                let recv_param_mono = param_monos.first().cloned();
                let recv_expr_scheme = self.ty_of(tcx, container_pat.id);
                let recv_value =
                    self.emit_pattern_value(container_pat.as_ref(), &recv_expr_scheme, tcx, src)?;
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

                let index_ty = self.ty_of(tcx, index_expr.id);
                let index_val = index_expr.lir_gen(self, tcx)?;
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
        tcx: &TyCtx,
        src: &Source,
    ) -> RayResult<lir::Value> {
        // Look up the type and generate RHS first
        let rhs_ty = self.ty_of(tcx, assign.rhs.id);
        let rhs_val = assign.rhs.lir_gen(self, tcx)?;
        let maybe_rhs_loc = self.get_or_set_local(rhs_val.clone(), rhs_ty.clone());

        self.emit_assign_to_pattern(
            operator_id,
            &assign.lhs,
            rhs_val,
            rhs_ty,
            maybe_rhs_loc,
            tcx,
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
        tcx: &TyCtx,
        src: &Source,
    ) -> RayResult<()> {
        match &lhs_pat.value {
            Pattern::Name(name) => {
                let Some(rhs_loc) = rhs_loc else {
                    log::debug!("  SKIP assign: rhs is unit");
                    return Ok(());
                };

                let lhs_ty = self.ty_of(tcx, lhs_pat.id);
                let binding = self.binding_for_node(lhs_pat.id).unwrap_or_else(|| {
                    panic!(
                        "missing binding for pattern {:#x} ({})",
                        lhs_pat.id, lhs_pat
                    )
                });
                let debug_name = name
                    .path
                    .name()
                    .unwrap_or_else(|| self.debug_name_for_binding(binding));
                let lhs_loc = self.ensure_local_for_binding(binding, debug_name, lhs_ty.clone());

                log::debug!("  EMIT: ${} = ${}", lhs_loc, rhs_loc);
                self.set_local(
                    lhs_loc,
                    lir::Atom::new(lir::Variable::Local(rhs_loc)).into(),
                );
                Ok(())
            }
            Pattern::Deref(Node { id, value: name }) => {
                let Some(rhs_loc) = rhs_loc else {
                    log::debug!("  SKIP assign: rhs is unit");
                    return Ok(());
                };

                let lhs_ty = self.ty_of(tcx, lhs_pat.id);
                let binding = self.binding_for_node(*id).unwrap_or_else(|| {
                    panic!(
                        "missing binding for pattern {:#x} ({})",
                        lhs_pat.id, lhs_pat
                    )
                });
                let debug_name = name
                    .path
                    .name()
                    .unwrap_or_else(|| self.debug_name_for_binding(binding));
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
                tcx,
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
                        tcx,
                        src,
                    )?;
                }

                Ok(())
            }
            Pattern::Some(_) => todo!("emit_assign_to_pattern: Pattern::Some"),
        }
    }

    fn emit_tuple(
        &mut self,
        ty: &TyScheme,
        items: &[Node<Expr>],
        tcx: &TyCtx,
    ) -> RayResult<lir::Value> {
        let tys = variant!(ty.mono(), if Ty::Tuple(tys));

        // create a new local for the tuple value
        let tuple_loc = self.local(ty.clone());
        if !items.is_empty() {
            // build tuple value with inserts
            for (index, (el, el_ty)) in items.iter().zip(tys.iter().cloned()).enumerate() {
                let el_val = el.lir_gen(self, tcx)?;
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
    fn lir_gen(&self, ctx: &mut GenCtx<'_>, _: &TyCtx) -> RayResult<GenResult> {
        let &(path, _) = self;
        let full_name = path.to_string();
        if let Some(&global) = ctx.global_idx.get(&full_name) {
            return Ok(lir::Variable::Global(ctx.path(), global).into());
        }

        panic!("unresolved value path `{}` (expected global)", full_name)
    }
}

impl LirGen<GenResult> for (&Literal, &TyScheme) {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>, _: &TyCtx) -> RayResult<GenResult> {
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
                // convert the string to bytes and add a `Data` to the program
                let bytes = s.as_bytes().to_vec();
                let len = bytes.len();
                let string_size = lir::Size::bytes(len);
                let idx = ctx.data(bytes);

                // allocate a pointer to store the string bytes
                let data_loc = ctx.local(Ty::ref_of(Ty::u8()).into());
                let ptr = lir::Malloc::new(Ty::u8().into(), lir::Atom::uptr(len as u64));
                ctx.set_local(data_loc, ptr.into());

                // make a call to `memcpy` to copy the bytes
                let path = ctx.path();
                ctx.push(lir::Inst::MemCopy(
                    lir::Variable::Local(data_loc), // dst
                    lir::Variable::Data(path, idx), // src
                    string_size.into(),             // size
                ));

                // create a `string` struct
                //  - raw_ptr: *u8
                //  - len: usize
                let loc = ctx.local(Ty::string().into());
                ctx.push(lir::Inst::StructInit(
                    lir::Variable::Local(loc),
                    StructTy {
                        kind: NominalKind::Struct,
                        path: "string".into(),
                        ty: Ty::string().into(),
                        fields: vec![
                            (str!("raw_ptr"), Ty::ref_of(Ty::u8()).into()),
                            (str!("len"), Ty::uint().into()),
                        ],
                    },
                ));

                // store the pointer to the bytes
                ctx.push(lir::SetField::new(
                    lir::Variable::Local(loc),
                    str!("raw_ptr"),
                    lir::Variable::Local(data_loc).into(),
                ));

                // store the size of the string
                ctx.push(lir::SetField::new(
                    lir::Variable::Local(loc),
                    str!("len"),
                    lir::Atom::Size(string_size).into(),
                ));

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

impl LirGen<GenResult> for (&Node<&ast::Func>, &TyScheme) {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>, tcx: &TyCtx) -> RayResult<GenResult> {
        let &(func, fn_ty) = self;
        let poly_ty = tcx.get_poly_ty(func.id);

        ctx.with_builder(lir::Builder::new());

        ctx.with_entry_block(|ctx| {
            // add the parameters to the function
            for p in func.sig.params.iter() {
                let path = p.name();
                let binding = ctx
                    .binding_for_node(p.id)
                    .unwrap_or_else(|| panic!("missing binding for param {:#x}", p.id));
                let key = path
                    .name()
                    .unwrap_or_else(|| ctx.debug_name_for_binding(binding));
                let ty = ctx.ty_of(tcx, p.id);
                ctx.param(binding, key, ty.into_mono());
            }
        });

        let body = func.body.as_ref().unwrap();
        let body_val = if !matches!(body.value, Expr::Block(_)) {
            let (_, value) = ctx.with_new_block(|ctx| body.lir_gen(ctx, tcx));
            value?
        } else {
            body.lir_gen(ctx, tcx)?
        };

        ctx.with_exit_block(|ctx| {
            log::debug!("[Func::lir_gen] function type = {:?}", fn_ty);
            let (_, _, _, ret_ty) = fn_ty
                .try_borrow_fn()
                .expect(&format!("function type, but found {:?}", fn_ty));
            let value = if !ret_ty.is_unit() {
                let body_ty = ctx.ty_of(tcx, body.id);
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

        let base = &func.sig.path;
        log::debug!("base function path: {}", base);
        log::debug!("function type: {}", fn_ty);
        if let Some(poly_ty) = poly_ty {
            log::debug!("poly function type: {}", poly_ty);
        }
        let name = if !fn_ty.is_polymorphic() {
            sema::fn_name(base, fn_ty)
        } else {
            base.value.clone()
        };

        log::debug!("function name: {}", name);
        let mut func = Node::with_id(
            func.id,
            lir::Func::new(
                base.value.clone(),
                fn_ty.clone(),
                func.sig.modifiers.clone(),
                symbols,
                cfg,
            ),
        );
        func.name = name;
        func.params = params;
        func.locals = locals;
        func.blocks = blocks;

        ctx.new_func(func);

        Ok(lir::Value::Empty)
    }
}

impl LirGen<GenResult> for UnaryOp {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>, tcx: &TyCtx) -> RayResult<GenResult> {
        ctx.call_from_op(self.op.id, &[self.expr.as_ref()], tcx)
    }
}

impl LirGen<GenResult> for BinOp {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>, tcx: &TyCtx) -> RayResult<GenResult> {
        ctx.call_from_op(self.op.id, &[self.lhs.as_ref(), self.rhs.as_ref()], tcx)
    }
}

impl LirGen<GenResult> for (&Call, &Source) {
    fn lir_gen(&self, _ctx: &mut GenCtx<'_>, _tcx: &TyCtx) -> RayResult<GenResult> {
        todo!("FIXME: this uses legacy code that needs to change")

        // let &(call, src) = self;
        // let callee_is_direct_fn = call
        //     .callee
        //     .path()
        //     .and_then(|path| ctx.maybe_direct_function(call.callee.id, path, tcx))
        //     .is_some();

        // let mut arg_exprs: Vec<(&Node<Expr>, TyScheme)> = Vec::new();
        // let mut base = if let Expr::Dot(dot) = &call.callee.value {
        //     let self_ty = tcx.ty_of(dot.lhs.id);
        //     log::debug!("[Call::lir_gen] type of {}: {}", dot.lhs, self_ty);
        //     arg_exprs.push((dot.lhs.as_ref(), self_ty));
        //     Some(dot.rhs.path.clone())
        // } else if let Expr::ScopedAccess(scoped_access) = &call.callee.value {
        //     if let Expr::Type(ty) = &scoped_access.lhs.value {
        //         let base = ty.value().mono().get_path().without_type_args();
        //         let member = scoped_access
        //             .rhs
        //             .value
        //             .path
        //             .name()
        //             .unwrap_or_else(|| scoped_access.rhs.value.to_string());
        //         Some(base.append(member))
        //     } else {
        //         None
        //     }
        // } else if callee_is_direct_fn {
        //     call.callee.path().cloned()
        // } else {
        //     None
        // };

        // let resolved = tcx.call_resolution(call.callee.id).cloned();
        // let fn_ty = if let Some(resolved) = &resolved {
        //     base = Some(resolved.base_fqn.clone());
        //     resolved.callee_ty.clone()
        // } else {
        //     TyScheme::from_mono(
        //         tcx.get_ty(call.callee.id)
        //             .unwrap_or_else(|| {
        //                 panic!(
        //                     "missing mono type for call callee {} ({:#x})",
        //                     call.callee, call.callee.id
        //                 )
        //             })
        //             .clone(),
        //     )
        // };

        // log::debug!("[lir_gen] scheme for call {}: {}", call, fn_ty);
        // log::debug!(
        //     "call: callee id={:#x} function type = {}",
        //     call.callee.id,
        //     fn_ty
        // );

        // let mut evaluated_callee: Option<lir::Value> = None;
        // if base.is_none() {
        //     let value = call.callee.lir_gen(ctx, tcx)?;
        //     evaluated_callee = Some(value);
        // }

        // for arg in call.args.items.iter() {
        //     arg_exprs.push((arg, ctx.ty_of(tcx, arg.id)));
        // }

        // let original_poly_ty = resolved
        //     .as_ref()
        //     .map(|resolved| resolved.poly_callee_ty.clone())
        //     .or_else(|| tcx.get_poly_ty(call.callee.id).cloned());

        // // Snapshot instantiated parameter types of the callee after substitution.
        // let param_monos = match fn_ty.mono() {
        //     Ty::Func(params, _) => params.clone(),
        //     _ => Vec::new(),
        // };

        // let recv_mode = base
        //     .as_ref()
        //     .map(|base| ctx.recv_mode_for_base(tcx, base))
        //     .unwrap_or_default();

        // let fn_name = if resolved.is_none() {
        //     base.clone().map(|base| {
        //         log::debug!("base_name: {}", base);
        //         if ctx.is_extern(&base) {
        //             ctx.extern_link_name(&base).unwrap_or(base)
        //         } else {
        //             sema::fn_name(&base, &fn_ty)
        //         }
        //     })
        // } else {
        //     None
        // };

        // let is_method_call = matches!(&call.callee.value, Expr::Dot(_));
        // let call_args =
        //     ctx.build_call_args(tcx, is_method_call, recv_mode, arg_exprs, &param_monos)?;

        // if let Some(resolved) = &resolved {
        //     return ctx.emit_resolved_direct_call(resolved, call_args, src);
        // }

        // if let Some(fn_name) = fn_name {
        //     log::debug!("poly_ty: {:?}", original_poly_ty);
        //     ctx.emit_named_direct_call(
        //         fn_name,
        //         call_args,
        //         fn_ty.clone(),
        //         original_poly_ty.clone(),
        //         src,
        //     )
        // } else {
        //     let callee_val = evaluated_callee
        //         .take()
        //         .map(Ok)
        //         .unwrap_or_else(|| call.callee.lir_gen(ctx, tcx))?;
        //     ctx.emit_fnhandle_call(
        //         tcx,
        //         call.callee.id,
        //         callee_val,
        //         call_args,
        //         original_poly_ty,
        //         src,
        //     )
        // }
    }
}

impl LirGen<GenResult> for Node<Expr> {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>, tcx: &TyCtx) -> RayResult<GenResult> {
        let ty = ctx.ty_of(tcx, self.id);
        Ok(match &self.value {
            Expr::Path(path) => {
                if let Some(fn_ty) = ctx.maybe_direct_function(self.id, path, tcx) {
                    let var = ctx.build_fn_handle_for_function(path.clone(), fn_ty);
                    lir::Value::new(var)
                } else {
                    let binding = ctx.binding_for_node(self.id);
                    if let Some(binding) = binding {
                        if let Some(global) = ctx.global_var_for_binding(binding) {
                            return Ok(global.into());
                        }
                        let debug_name = ctx.debug_name_for_binding(binding);
                        let loc = ctx.ensure_local_for_binding(binding, debug_name, ty.clone());
                        lir::Value::new(lir::Variable::Local(loc))
                    } else {
                        (path, &ty).lir_gen(ctx, tcx)?
                    }
                }
            }
            Expr::Name(n) => {
                if let Some(fn_ty) = ctx.maybe_direct_function(self.id, &n.path, tcx) {
                    let var = ctx.build_fn_handle_for_function(n.path.clone(), fn_ty);
                    lir::Value::new(var)
                } else {
                    let binding = ctx
                        .binding_for_node(self.id)
                        .unwrap_or_else(|| panic!("missing binding for name expr {:#x}", self.id));
                    if let Some(global) = ctx.global_var_for_binding(binding) {
                        return Ok(global.into());
                    }
                    let debug_name = n
                        .path
                        .name()
                        .unwrap_or_else(|| ctx.debug_name_for_binding(binding));
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

                    if let Some(fn_ty) = ctx.maybe_direct_function(self.id, &path, tcx) {
                        let var = ctx.build_fn_handle_for_function(path, fn_ty);
                        lir::Value::new(var)
                    } else {
                        // Fallback: treat it as a global value path.
                        (&path, &ty).lir_gen(ctx, tcx)?
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
                expr.lir_gen(ctx, tcx)?
            }
            Expr::Literal(lit) => (lit, &ty).lir_gen(ctx, tcx)?,
            Expr::Paren(ex) | Expr::TypeAnnotated(ex, _) => ex.lir_gen(ctx, tcx)?,
            Expr::New(new) => {
                let count = match &new.count {
                    Some(c) => {
                        let ty = ctx.ty_of(tcx, c.id);
                        let value = c.lir_gen(ctx, tcx)?;
                        lir::Variable::Local(ctx.get_or_set_local(value, ty).unwrap()).into()
                    }
                    _ => lir::Atom::uptr(1),
                };
                lir::Malloc::new(new.ty.deref().deref().clone().into(), count)
            }
            Expr::Cast(c) => {
                let src = c.lhs.lir_gen(ctx, tcx)?;
                let lhs_ty = ctx.ty_of(tcx, c.lhs.id);
                let loc = ctx.get_or_set_local(src, lhs_ty).unwrap();
                lir::Cast::new(lir::Variable::Local(loc), c.ty.deref().clone())
            }
            Expr::Range(range) => {
                // create a `range` struct
                //  - start: T
                //  - end: T
                //  - inclusive: bool
                let loc = ctx.local(ty.clone());
                let el_ty = ctx.ty_of(tcx, range.start.id);

                ctx.push(lir::Inst::StructInit(
                    lir::Variable::Local(loc),
                    StructTy {
                        kind: NominalKind::Struct,
                        path: "range".into(),
                        ty: Ty::range(el_ty.mono().clone()).into(),
                        fields: vec![
                            ("start".to_string(), el_ty.clone()),
                            ("end".to_string(), el_ty.clone()),
                            ("inclusive".to_string(), Ty::bool().into()),
                        ],
                    },
                ));

                // store the start value
                let start_val = range.start.lir_gen(ctx, tcx)?;
                let start_loc = ctx.get_or_set_local(start_val, el_ty.clone()).unwrap();

                ctx.push(lir::SetField::new(
                    lir::Variable::Local(loc),
                    str!("start"),
                    lir::Variable::Local(start_loc).into(),
                ));

                // store the end value
                let end_val = range.end.lir_gen(ctx, tcx)?;
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
                        let lhs_val = dot.lhs.lir_gen(ctx, tcx)?;
                        let lhs_ty = ctx.ty_of(tcx, dot.lhs.id);
                        let lhs_loc = ctx.get_or_set_local(lhs_val, lhs_ty.clone()).unwrap();

                        let offset =
                            lir::LeaOffset::Field(lhs_ty.clone(), dot.rhs.path.to_short_name());

                        (
                            lir::Value::Atom(lir::Variable::Local(lhs_loc).into()),
                            offset,
                        )
                    }
                    _ => (rf.expr.lir_gen(ctx, tcx)?, lir::LeaOffset::zero()),
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
                let ptr_ty = ctx.ty_of(tcx, deref.expr.id); // *T/rawptr[T]
                let value = deref.expr.lir_gen(ctx, tcx)?;
                let loc = ctx.get_or_set_local(value, ptr_ty).unwrap();
                let src = lir::Variable::Local(loc);

                lir::Load::new(src, lir::Size::zero())
            }
            Expr::List(list) => {
                todo!("FIXME: this uses legacy code that needs to change")

                // let item_count = list.items.len();
                // let capacity = (item_count * 3) as u64;

                // // allocate memory for the values
                // let el_ty = ty.mono().type_argument_at(0).unwrap();
                // let values_loc = ctx.local(Ty::ref_of(el_ty.clone()).into());
                // let values_ptr = lir::Malloc::new(el_ty.clone().into(), lir::Atom::uptr(capacity));
                // ctx.set_local(values_loc, values_ptr.into());

                // let mut offset: usize = 0;
                // for item in list.items.iter() {
                //     let item_val = item.lir_gen(ctx, tcx)?;
                //     let item_ty = ctx.ty_of(tcx, item.id);
                //     if let Some(item_loc) = ctx.get_or_set_local(item_val, item_ty) {
                //         ctx.push(lir::Store::new(
                //             lir::Variable::Local(values_loc),
                //             lir::Variable::Local(item_loc).into(),
                //             offset,
                //         ));
                //     }

                //     offset += 1;
                // }

                // let list_loc = ctx.local(ty.clone());
                // let list_fqn = ctx.ncx.builtin_ty("list");
                // ctx.push(lir::Inst::StructInit(
                //     lir::Variable::Local(list_loc),
                //     StructTy {
                //         kind: NominalKind::Struct,
                //         path: list_fqn.clone(),
                //         ty: Ty::proj(list_fqn, vec![el_ty.clone()]).into(),
                //         fields: vec![
                //             ("values".to_string(), Ty::ref_of(el_ty.clone()).into()),
                //             ("len".to_string(), Ty::uint().into()),
                //             ("capacity".to_string(), Ty::uint().into()),
                //         ],
                //     },
                // ));

                // // store the values ptr
                // ctx.push(lir::SetField::new(
                //     lir::Variable::Local(list_loc),
                //     str!("values"),
                //     lir::Variable::Local(values_loc).into(),
                // ));

                // // store the length
                // ctx.push(lir::SetField::new(
                //     lir::Variable::Local(list_loc),
                //     str!("len"),
                //     lir::Atom::uptr(item_count as u64).into(),
                // ));

                // // store the capacity
                // ctx.push(lir::SetField::new(
                //     lir::Variable::Local(list_loc),
                //     str!("capacity"),
                //     lir::Atom::uptr(capacity as u64).into(),
                // ));

                // lir::Variable::Local(list_loc).into()
            }
            Expr::Curly(curly) => {
                let loc = ctx.local(ty.clone());
                let fields = curly
                    .elements
                    .iter()
                    .map(|elem| {
                        let (name, expr) = variant!(&elem.value, if CurlyElement::Labeled(x, y));
                        let elem_ty = ctx.ty_of(tcx, expr.id);
                        (name.path.name().unwrap(), elem_ty)
                    })
                    .collect();

                let kind = tcx.nominal_kind(ty.mono()).unwrap();
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
                    let field_ty = ctx.ty_of(tcx, field_value.id);
                    let val = field_value.lir_gen(ctx, tcx)?;
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
                let with_capacity_name = sema::fn_name(&with_capacity_base, &with_capacity_ty);
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
                let insert_name = sema::fn_name(&insert_base, &insert_fn_ty);

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
                    let key_scheme = ctx.ty_of(tcx, key.id);
                    let key_val = key.lir_gen(ctx, tcx)?;
                    let key_var = ctx.value_to_local_or_unit(key_val, key_scheme);

                    let value_scheme = ctx.ty_of(tcx, value.id);
                    let value_val = value.lir_gen(ctx, tcx)?;
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
                        let value = stmt.lir_gen(ctx, tcx)?;
                        if let Some(i) = value.to_inst() {
                            ctx.push(i);
                        }
                    }

                    last.lir_gen(ctx, tcx)?
                }
                None => lir::Value::Empty,
            },
            Expr::Boxed(boxed) => {
                let ptr_loc = ctx.local(ty.clone());
                let pointee_ty = variant!(ty.mono(), if Ty::Ref(p));
                let ptr_malloc =
                    lir::Malloc::new(pointee_ty.as_ref().clone().into(), lir::Atom::uptr(1));

                ctx.set_local(ptr_loc, ptr_malloc);
                let value = boxed.inner.lir_gen(ctx, tcx)?;
                ctx.push(lir::Store::new(lir::Variable::Local(ptr_loc), value, 0));

                lir::Variable::Local(ptr_loc).into()
            }
            Expr::Assign(assign) => {
                let src = ctx.srcmap.get(self);
                ctx.emit_assign_expr(self.id, assign, tcx, &src)?
            }
            Expr::Func(_) => todo!(),
            Expr::Dot(dot) => {
                let lhs_val = dot.lhs.lir_gen(ctx, tcx)?;
                let lhs_ty = ctx.ty_of(tcx, dot.lhs.id);
                let lhs_loc = ctx.get_or_set_local(lhs_val, lhs_ty.clone()).unwrap();

                lir::GetField {
                    src: lir::Variable::Local(lhs_loc),
                    field: dot.rhs.path.name().unwrap(),
                }
                .into()
            }
            Expr::Call(call) => {
                let src = ctx.srcmap.get(self);
                (call, &src).lir_gen(ctx, tcx)?
            }
            Expr::BinOp(binop) => binop.lir_gen(ctx, tcx)?,
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
                let captures = ctx.collect_closure_captures(self.id, tcx);
                let env_ty = ctx.ensure_closure_env_type(self.id, &captures);
                let fn_name = ctx.lower_closure(self, closure, &captures, &env_ty, tcx)?;
                let env = ctx.build_closure_env(&captures, &env_ty)?;
                let fn_ty_with_env = ctx
                    .closure_fn_types
                    .get(&self.id)
                    .expect("missing lowered closure fn type")
                    .clone();
                let closure_value_ty = ctx.ensure_closure_value_type(self.id, &fn_ty_with_env);
                let poly_ty = tcx.get_poly_ty(self.id).cloned();
                let handle = ctx.build_closure_value(
                    &closure_value_ty,
                    fn_name,
                    fn_ty_with_env.clone(),
                    env,
                    &env_ty,
                    poly_ty,
                )?;
                handle.into()
            }
            Expr::DefaultValue(_) => todo!("lir_gen: Expr::DefaultValue: {}", self.value),
            Expr::For(for_loop) => {
                let src = ctx.srcmap.get(self);

                let iterable_scheme = ctx.ty_of(tcx, for_loop.expr.id);
                let iterable_val = for_loop.expr.lir_gen(ctx, tcx)?;
                let iterable_loc = ctx
                    .get_or_set_local(iterable_val, iterable_scheme.clone())
                    .unwrap_or_else(|| panic!("expected non-unit iterable expression in `for`"));

                let iterable_trait_fqn = ItemPath::from(&ctx.ncx.builtin_ty("Iterable"));
                let iter_trait_fqn = ItemPath::from(&ctx.ncx.builtin_ty("Iter"));

                let container_mono = iterable_scheme.mono().clone();
                let elem_scheme = ctx.ty_of(tcx, for_loop.pat.id);
                let elem_mono = elem_scheme.mono().clone();

                let it_mono = ctx
                    .select_iterable_iterator_ty(
                        &iterable_trait_fqn,
                        &container_mono,
                        &elem_mono,
                        tcx,
                    )
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
                        tcx,
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
                            tcx,
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
                        tcx,
                        &for_loop.pat,
                        &elem_scheme,
                        elem_val,
                        cond_label,
                        &for_loop.body,
                        &src,
                    )?;
                    if handled {
                        return Ok(());
                    }

                    let body_val = for_loop.body.lir_gen(ctx, tcx)?;
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
                let mut some_binding: Option<(BindingId, String, usize)> = None;

                let cond_label = ctx.new_block();
                let cond_loc = ctx.with_block(cond_label, |ctx| {
                    ctx.block().markers_mut().push(lir::ControlMarker::If);
                    // Special-case `if some(pat) = expr { ... }` by lowering
                    // the condition to a check of the `is_some` field on the
                    // `nilable['a]` value produced by `expr`, and, for the
                    // simple `some(name)` case, binding `name` to the payload.
                    let cond_val = match &if_ex.cond.value {
                        Expr::Assign(assign) if matches!(assign.lhs.value, Pattern::Some(_)) => {
                            let rhs_ty = ctx.ty_of(tcx, assign.rhs.id);
                            let rhs_val = assign.rhs.lir_gen(ctx, tcx)?;
                            let rhs_loc = ctx.get_or_set_local(rhs_val, rhs_ty.clone()).unwrap();

                            if let Pattern::Some(inner_pat) = &assign.lhs.value {
                                let some_binder: Option<(BindingId, String)> = match &inner_pat.value {
                                    Pattern::Name(name) => {
                                        let binding = ctx.binding_for_node(inner_pat.id).unwrap_or_else(|| {
                                            panic!("missing binding for `some(name)` pattern {:#x}", inner_pat.id)
                                        });
                                        let debug_name = name
                                            .path
                                            .name()
                                            .unwrap_or_else(|| ctx.debug_name_for_binding(binding));
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
                                            .unwrap_or_else(|| ctx.debug_name_for_binding(binding));
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
                        _ => if_ex.cond.lir_gen(ctx, tcx)?,
                    };
                    RayResult::Ok(ctx.get_or_set_local(cond_val, Ty::bool().into()).unwrap())
                });

                // in the _current_ block, goto the condition
                ctx.goto(cond_label);

                let then_ty = ctx.ty_of(tcx, if_ex.then.id);
                let then_label = ctx.new_block();
                let (then_val, then_end) = ctx.with_block_capture(then_label, |ctx| {
                    // Install the binding for `some(name)` in the then-branch
                    // so that references to `name` see the payload local.
                    if let Some((binding, ref name, payload_loc)) = some_binding {
                        ctx.set_var(binding, name.clone(), payload_loc);
                    }
                    RayResult::Ok(if_ex.then.lir_gen(ctx, tcx)?)
                });

                let then_val = then_val?;
                let then_has_value = !matches!(then_val, lir::Value::Empty);
                let else_label = ctx.new_block();
                let (else_val, else_end) = ctx.with_block_capture(else_label, |ctx| {
                    RayResult::Ok(if let Some(else_ex) = if_ex.els.as_deref() {
                        // let else_ty = tcx.ty_of(else_ex.id);
                        Some(else_ex.lir_gen(ctx, tcx)?)
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
                let resolved = tcx.call_resolution(self.id).cloned().unwrap_or_else(|| {
                    panic!("missing call resolution for index expr {:#x}", self.id)
                });

                let param_monos = match resolved.callee_ty.mono() {
                    Ty::Func(params, _) => params.clone(),
                    _ => Vec::new(),
                };

                let recv_mode = ctx.recv_mode_for_base(tcx, &resolved.base_fqn);
                let call_args = ctx.build_call_args(
                    tcx,
                    true,
                    recv_mode,
                    vec![
                        (index.lhs.as_ref(), tcx.ty_of(index.lhs.id)),
                        (index.index.as_ref(), tcx.ty_of(index.index.id)),
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
                    let val = ex.lir_gen(ctx, tcx)?;
                    ctx.ret(val);
                } else {
                    // Bare `return` in a function whose Ray return type is `unit`.
                    ctx.ret(lir::Value::Empty);
                }
                lir::Value::Empty
            }
            Expr::Sequence(seq) => ctx.emit_tuple(&ty, &seq.items, tcx)?,
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
                let with_capacity_name = sema::fn_name(&with_capacity_base, &with_capacity_ty);
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
                let insert_name = sema::fn_name(&insert_base, &insert_fn_ty);

                let recv_val: lir::Value = lir::Variable::Local(set_loc).into();
                let recv_var = ctx
                    .maybe_coerce_receiver_arg(recv_val, &ty, &insert_recv_param, ReceiverMode::Ptr)
                    .unwrap_or_else(|| {
                        panic!("could not build receiver arg for set.insert: set_ty={}", ty)
                    });

                for item in set.items.iter() {
                    let item_scheme = ctx.ty_of(tcx, item.id);
                    let item_val = item.lir_gen(ctx, tcx)?;
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
            Expr::Tuple(tuple) => ctx.emit_tuple(&ty, &tuple.seq.items, tcx)?,
            Expr::Type(ty) => lir::Value::Type(ty.clone_value()),
            Expr::UnaryOp(unop) => unop.lir_gen(ctx, tcx)?,
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

                    let cond_val = while_stmt.cond.lir_gen(ctx, tcx)?;
                    let cond_loc = ctx.get_or_set_local(cond_val, Ty::bool().into()).unwrap();
                    ctx.cond(cond_loc, body_label, end_label);

                    ctx.with_block(body_label, |ctx| {
                        let body_val = while_stmt.body.lir_gen(ctx, tcx)?;
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
                let inner_ty = ctx.ty_of(tcx, inner.id);
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
                let inner_val = inner.lir_gen(ctx, tcx)?;
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
    fn lir_gen(&self, ctx: &mut GenCtx<'_>, tcx: &TyCtx) -> RayResult<GenResult> {
        log::debug!("getting type of {:#x}: {:?}", self.id, self);
        match &self.value {
            Decl::Func(func) => {
                let node = Node::with_id(self.id, func);
                let ty = tcx
                    .get_poly_ty(node.id)
                    .cloned()
                    .unwrap_or_else(|| ctx.ty_of(tcx, self.id));
                return (&node, &ty).lir_gen(ctx, tcx);
            }
            Decl::Mutable(_) | Decl::Name(_) => {
                todo!()
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
                        let ty = ctx.ty_of(tcx, const_node.lhs.id);
                        let name = const_node.lhs.path().unwrap();
                        let init_value = const_node.rhs.lir_gen(ctx, tcx)?;
                        ctx.new_global(name, init_value, ty, false);
                    }
                }

                if let Some(funcs) = &imp.funcs {
                    for decl in funcs {
                        let Decl::Func(func) = &decl.value else {
                            unreachable!("impl funcs should only contain Decl::Func");
                        };
                        let func_node = Node {
                            id: decl.id,
                            value: func,
                        };
                        let ty = tcx
                            .get_poly_ty(decl.id)
                            .cloned()
                            .unwrap_or_else(|| ctx.ty_of(tcx, decl.id));
                        log::debug!(
                            "[lir_gen] generate impl func: ty = {}, sig = {:?}",
                            ty,
                            func.sig
                        );
                        (&func_node, &ty).lir_gen(ctx, tcx)?;
                    }
                }
            }
            Decl::Extern(ext) => {
                let decl = ext.decl();
                let src = ext.src();
                let has_intrinsic = ctx.srcmap.has_intrinsic(self);
                log::debug!(
                    "[Decl::lir_gen] has_intrinsic={}: {:?}",
                    has_intrinsic,
                    self
                );
                let intrinsic_kind = if has_intrinsic {
                    lir::IntrinsicKind::from_path(match decl {
                        Decl::FnSig(sig) => &sig.path.value,
                        Decl::Mutable(name) | Decl::Name(name) => &name.path,
                        _ => unreachable!("unexpected extern declaration {:?}", decl),
                    })
                } else {
                    None
                };
                match ext.decl() {
                    Decl::Mutable(name) | Decl::Name(name) => {
                        let is_mutable = matches!(decl, Decl::Mutable(_));
                        let ty = ctx.ty_of(tcx, name.id);
                        let map_name = name.path.clone();
                        ctx.new_extern(
                            map_name.clone(),
                            map_name,
                            ty,
                            is_mutable,
                            vec![],
                            has_intrinsic,
                            intrinsic_kind.clone(),
                            src.clone(),
                        );
                    }
                    Decl::FnSig(sig) => {
                        let ty = tcx.ty_of(self.id);
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
                            src.clone(),
                        );
                    }
                    d @ _ => unreachable!("lir_gen Decl::Extern: {:?}", d),
                }
            }
            Decl::Declare(_) => todo!(),
            Decl::FnSig(_) => todo!(),
            Decl::TypeAlias(_, _) | Decl::Struct(_) => {}
        }

        Ok(lir::Value::Empty)
    }
}

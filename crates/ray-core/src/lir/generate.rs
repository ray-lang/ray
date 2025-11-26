use std::{cell::RefCell, collections::HashMap, ops::Deref, rc::Rc};

use ray_shared::pathlib::Path;
use ray_typing::top::{Subst, Substitutable, mgu};
use ray_typing::{
    TyCtx,
    ty::{NominalKind, ReceiverMode, StructTy, Ty, TyScheme, TyVar},
};

use crate::{
    ast::{
        self, CurlyElement, Decl, Expr, Literal, Modifier, Module, Node, Pattern, PrefixOp,
        RangeLimits, UnaryOp, token::IntegerBase,
    },
    errors::RayResult,
    lir::{self, types::SizeOf},
    sema,
    sourcemap::SourceMap,
};

use super::START_FUNCTION;

fn extract_some_binding_name<'a>(pat: &'a Pattern) -> Option<&'a ast::Name> {
    match pat {
        Pattern::Name(n) => Some(n),
        Pattern::Deref(Node { value: n, .. }) => Some(n),
        _ => None,
    }
}

impl lir::Program {
    pub fn generate(
        module: &Module<(), Decl>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
        libs: Vec<lir::Program>,
    ) -> RayResult<lir::Program> {
        let path = module.path.clone();
        let prog = Rc::new(RefCell::new(lir::Program::new(path)));
        let start_idx = {
            let mut ctx = GenCtx::new(Rc::clone(&prog), srcmap);
            module.decls.lir_gen(&mut ctx, tcx)?;

            let module_main_path = prog.borrow().main_path();
            let user_main_path = prog.borrow().user_main_path();

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

            let user_main_resolved_path = {
                let prog_ref = prog.borrow();
                prog_ref
                    .funcs
                    .iter()
                    .find_map(|f| f.name.starts_with(&user_main_path).then(|| f.name.clone()))
            };

            if !module.is_lib {
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
                                Subst::new(),
                            )
                            .into(),
                        );
                    }

                    if let Some(user_main_path) = user_main_resolved_path {
                        log::debug!("calling user main function: {}", user_main_path);
                        main_symbols.insert(user_main_path.clone());
                        ctx.push(
                            lir::Call::new(
                                user_main_path.clone(),
                                vec![],
                                Ty::Func(vec![], Box::new(Ty::unit())).into(),
                                None,
                                Subst::new(),
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
            }
        };

        // take the prog out of the pointer
        let mut prog = Rc::try_unwrap(prog).unwrap().into_inner();
        prog.start_idx = start_idx;
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
        let user_main_path = self.user_main_path();
        let mut i = 0;
        while i < self.funcs.len() {
            let f = &self.funcs[i];
            if f.name == START_FUNCTION {
                self.start_idx = i as i64;
            } else if f.name.starts_with(&user_main_path) {
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
    fn new(prog: Rc<RefCell<lir::Program>>, srcmap: &'a SourceMap) -> GenCtx<'a> {
        // let scope = prog.borrow().module_path.clone();
        GenCtx {
            prog,
            builder: None,
            data_idx: HashMap::new(),
            global_idx: HashMap::new(),
            srcmap,
        }
    }

    fn ty_of(&self, tcx: &TyCtx, id: u64) -> TyScheme {
        tcx.instantiate_scheme(tcx.ty_of(id))
    }

    fn with_builder(&mut self, builder: lir::Builder) {
        self.builder = Some(builder);
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
        prog.trait_member_set.insert(name);
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
            self.push(lir::Inst::SetLocal(idx.into(), value));
            Some(idx)
        }
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
        let last_block = self.curr_block;
        self.curr_block = prev_block;
        (last_block, t)
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

    pub fn call_from_op<O>(
        &mut self,
        func_fqn: &mut Path,
        trait_fqn: &Path,
        op: &Node<O>,
        args: &[&Node<Expr>],
        fn_ty: &TyScheme,
        tcx: &TyCtx,
    ) -> RayResult<GenResult> {
        let mut fn_ty = tcx.instantiate_scheme(fn_ty.clone());
        let original_poly_ty = tcx.get_poly_ty(op.id).cloned();
        let mut poly_ty = original_poly_ty
            .clone()
            .map(|ty| tcx.instantiate_scheme(ty));
        let mut arg_tys = args
            .iter()
            .map(|arg| tcx.instantiate_scheme(tcx.ty_of(arg.id)))
            .collect::<Vec<_>>();
        log::debug!(
            "call_from_op before subst: fn_ty={} args={}",
            fn_ty,
            arg_tys
                .iter()
                .map(|ty| ty.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        let mut subst = fn_ty.instantiate_fn_with_args(poly_ty.as_mut(), &mut arg_tys);
        log::debug!("subst: {}", subst);
        if !subst.is_empty() {
            func_fqn.apply_subst(&subst);
        }
        log::debug!("func_fqn: {}", func_fqn);

        let base = trait_fqn.merge(&func_fqn);

        log::debug!("base_name: {}", base);
        let fn_name = if !self.is_extern(&base) {
            if fn_ty.is_polymorphic() {
                poly_ty
                    .as_ref()
                    .map(|poly| sema::fn_name(&base, poly))
                    .unwrap_or_else(|| sema::fn_name(&base, &fn_ty))
            } else {
                sema::fn_name(&base, &fn_ty)
            }
        } else {
            base
        };

        if let (Some(orig_poly), Some(inst_poly)) = (original_poly_ty.as_ref(), poly_ty.as_ref()) {
            if let Ok((_, poly_subst)) = mgu(orig_poly.mono(), inst_poly.mono()) {
                subst.union(poly_subst);
            }
        }

        let mut call_args: Vec<lir::Variable> = vec![];
        for (idx, (arg, arg_ty)) in args.iter().zip(arg_tys.iter()).enumerate() {
            log::debug!("call_from_op arg[{}] id={:#x} ty={}", idx, arg.id, arg_ty);
            let arg_val = arg.lir_gen(self, tcx)?;

            if let Some(arg_loc) = self.get_or_set_local(arg_val, arg_ty.clone()) {
                call_args.push(lir::Variable::Local(arg_loc));
            } else {
                call_args.push(lir::Variable::Unit)
            }
        }
        log::debug!("add sym: {}", fn_name);
        self.add_sym(fn_name.clone());
        Ok(lir::Call::new(fn_name, call_args, fn_ty.clone(), original_poly_ty, subst).into())
    }
}

pub type GenResult = lir::Value;

impl LirGen<GenResult> for (&Pattern, &TyScheme) {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>, tcx: &TyCtx) -> RayResult<GenResult> {
        let &(pat, ty) = self;
        match pat {
            Pattern::Name(name) | Pattern::Deref(Node { id: _, value: name }) => {
                let name = name.to_string();
                let idx = ctx.get_var(&name).copied().unwrap_or_else(|| {
                    // this variable is not referenced in the current block
                    let idx = ctx.local(ty.clone());
                    ctx.set_var(name.clone(), idx);
                    idx
                });
                Ok(lir::Value::new(lir::Variable::Local(idx)))
            }
            Pattern::Dot(lhs, rhs) => {
                // For pattern-as-value contexts (rare), read the field value like `Expr::Dot`.
                // We compute the base value/local, then produce a GetField value.
                let lhs_ty = ctx.ty_of(tcx, lhs.id);
                let lhs_val = (&lhs.value, &lhs_ty).lir_gen(ctx, tcx)?;
                let lhs_loc = ctx.get_or_set_local(lhs_val, lhs_ty.clone()).unwrap();

                Ok(lir::GetField {
                    src: lir::Variable::Local(lhs_loc),
                    field: rhs.path.name().unwrap(),
                }
                .into())
            }
            Pattern::Missing(_) => todo!(),
            Pattern::Sequence(_) => todo!(),
            Pattern::Some(_) => todo!(),
            Pattern::Tuple(_) => todo!(),
        }
    }
}

impl LirGen<GenResult> for (&Path, &TyScheme) {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>, _: &TyCtx) -> RayResult<GenResult> {
        let &(path, ty) = self;
        let name = path.to_string();
        if let Some(&global) = ctx.global_idx.get(&name) {
            return Ok(lir::Variable::Global(ctx.path(), global).into());
        }

        let loc = ctx.get_var(&name).copied().unwrap_or_else(|| {
            log::debug!("define local variable: {} of type {}", name, ty);
            // variable not defined in the current block
            let idx = ctx.local(ty.clone());
            ctx.set_var(name.clone(), idx);
            idx
        });
        Ok(lir::Variable::Local(loc).into())
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
                let data_loc = ctx.local(Ty::refty(Ty::u8()).into());
                let ptr = lir::Malloc::new(Ty::u8().into(), lir::Atom::uptr(len as u64));
                ctx.push(lir::Inst::SetLocal(data_loc.into(), ptr.into()));

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
                            (str!("raw_ptr"), Ty::refty(Ty::u8()).into()),
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
                    ctx.push(lir::Inst::SetLocal(
                        is_some_loc.into(),
                        lir::Atom::BoolConst(false).into(),
                    ));
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
                let name = p.name().to_string();
                let ty = ctx.ty_of(tcx, p.id);
                ctx.param(name, ty.into_mono());
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
                let body_loc = ctx
                    .get_or_set_local(body_val, ctx.ty_of(tcx, body.id))
                    .unwrap();
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
        let fn_ty = ctx.ty_of(tcx, self.op.id);
        let name = self.op.to_string();
        let (mut func_fqn, trait_fqn) = tcx.lookup_prefix_op(&name).cloned().unwrap();
        log::debug!("trait_fqn: {}", trait_fqn);
        log::debug!("func_fqn: {}", func_fqn);

        ctx.call_from_op(
            &mut func_fqn,
            &trait_fqn,
            &self.op,
            &[self.expr.as_ref()],
            &fn_ty,
            tcx,
        )
    }
}

impl LirGen<GenResult> for Node<Expr> {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>, tcx: &TyCtx) -> RayResult<GenResult> {
        let ty = ctx.ty_of(tcx, self.id);
        Ok(match &self.value {
            Expr::Path(v) => (v, &ty).lir_gen(ctx, tcx)?,
            Expr::Name(n) => (&n.path, &ty).lir_gen(ctx, tcx)?,
            Expr::Pattern(p) => (p, &ty).lir_gen(ctx, tcx)?,
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
                ctx.push(lir::Inst::SetLocal(
                    bool_loc.into(),
                    lir::Atom::UintConst(
                        if matches!(range.limits, RangeLimits::Inclusive) {
                            1
                        } else {
                            0
                        },
                        lir::Size::bytes(1),
                    )
                    .into(),
                ));

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
            Expr::Tuple(tuple) => {
                let tys = variant!(ty.mono(), if Ty::Tuple(tys));

                // create a new local for the tuple and then make an allocation
                let tuple_loc = ctx.local(ty.clone());
                let size = ty.mono().size_of();
                if !size.is_zero() {
                    // for each element of the tuple
                    let mut offset = lir::Size::zero();
                    for (el, ty) in tuple.seq.items.iter().zip(tys.iter().cloned()) {
                        // generate the lir for the element
                        let val = el.lir_gen(ctx, tcx)?;
                        let size = ty.size_of();
                        if let Some(el_loc) = ctx.get_or_set_local(val, ty.into()) {
                            // store the element
                            ctx.push(lir::Store::new(
                                lir::Variable::Local(tuple_loc),
                                lir::Atom::new(lir::Variable::Local(el_loc)).into(),
                                offset,
                            ));
                        }

                        offset += size;
                    }

                    lir::Value::new(lir::Variable::Local(tuple_loc))
                } else {
                    lir::Value::new(lir::Atom::NilConst)
                }
            }
            Expr::List(list) => {
                let item_count = list.items.len();
                let capacity = (item_count * 3) as u64;

                // allocate memory for the values
                let el_ty = ty.mono().get_ty_param_at(0).unwrap();
                let el_size = el_ty.size_of();
                let values_loc = ctx.local(Ty::refty(el_ty.clone()).into());
                let values_ptr = lir::Malloc::new(el_ty.clone().into(), lir::Atom::uptr(capacity));
                ctx.push(lir::Inst::SetLocal(values_loc.into(), values_ptr.into()));

                let mut offset = lir::Size::zero();
                for item in list.items.iter() {
                    let item_val = item.lir_gen(ctx, tcx)?;
                    if let Some(item_loc) = ctx.get_or_set_local(item_val, ctx.ty_of(tcx, item.id))
                    {
                        ctx.push(lir::Store::new(
                            lir::Variable::Local(values_loc),
                            lir::Variable::Local(item_loc).into(),
                            offset,
                        ));
                    }

                    offset += el_size;
                }

                let list_loc = ctx.local(ty.clone());
                ctx.push(lir::Inst::StructInit(
                    lir::Variable::Local(list_loc),
                    StructTy {
                        kind: NominalKind::Struct,
                        path: "list".into(),
                        ty: Ty::list(el_ty.clone()).into(),
                        fields: vec![
                            ("values".to_string(), Ty::refty(el_ty.clone()).into()),
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
                        let (name, _) = variant!(&elem.value, if CurlyElement::Labeled(x, y));
                        let elem_ty = ctx.ty_of(tcx, elem.id);
                        (name.path.name().unwrap(), elem_ty)
                    })
                    .collect();

                let kind = ty.mono().nominal_kind(tcx).unwrap();
                ctx.push(lir::Inst::StructInit(
                    lir::Variable::Local(loc),
                    StructTy {
                        kind,
                        path: ty.mono().get_path(),
                        ty: ty.clone(),
                        fields,
                    },
                ));

                let mut field_insts = vec![];
                for field in curly.elements.iter() {
                    let (name, field_value) =
                        variant!(&field.value, if CurlyElement::Labeled(x, y));
                    let field_ty = ctx.ty_of(tcx, field.id);
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
            Expr::Block(block) => {
                let mut values = block.stmts.lir_gen(ctx, tcx)?;
                let last = values.pop();
                for value in values {
                    if let Some(i) = value.to_inst() {
                        ctx.push(i);
                    }
                }

                last.unwrap_or_default()
            }
            Expr::Boxed(boxed) => {
                let ptr_loc = ctx.local(ty.clone());
                let pointee_ty = variant!(ty.mono(), if Ty::Ref(p));
                let ptr_malloc =
                    lir::Malloc::new(pointee_ty.as_ref().clone().into(), lir::Atom::uptr(1));

                ctx.push(lir::Inst::SetLocal(ptr_loc, ptr_malloc));
                let value = boxed.inner.lir_gen(ctx, tcx)?;
                ctx.push(lir::Store::new(
                    lir::Variable::Local(ptr_loc),
                    value,
                    lir::Size::zero(),
                ));

                lir::Variable::Local(ptr_loc).into()
            }
            Expr::Assign(assign) => {
                // Look up the type and generate RHS first
                let rhs_ty = ctx.ty_of(tcx, assign.rhs.id);
                let rhs_val = assign.rhs.lir_gen(ctx, tcx)?;
                let maybe_rhs_loc = ctx.get_or_set_local(rhs_val, rhs_ty);

                // If the LHS is a field projection (`a.x = expr`), emit SetField instead of SetLocal.
                if let Pattern::Dot(base_pat, field_name) = &assign.lhs.value {
                    let base_ty = ctx.ty_of(tcx, base_pat.id);
                    let base_val = (&base_pat.value, &base_ty).lir_gen(ctx, tcx)?;
                    if let (Some(base_loc), Some(rhs_loc)) = (
                        ctx.get_or_set_local(base_val, base_ty.clone()),
                        maybe_rhs_loc,
                    ) {
                        ctx.push(lir::SetField::new(
                            lir::Variable::Local(base_loc),
                            field_name.path.name().unwrap(),
                            lir::Variable::Local(rhs_loc).into(),
                        ));
                    }
                    return Ok(lir::Value::Empty);
                }

                // Otherwise, compute the LHS location and fall back to normal SetLocal/Store
                let lhs_ty = ctx.ty_of(tcx, assign.lhs.id);
                let lhs_val = (&assign.lhs.value, &lhs_ty).lir_gen(ctx, tcx)?;
                let maybe_lhs_loc = ctx.get_or_set_local(lhs_val, lhs_ty.clone());

                log::debug!("ASSIGN {:?} := {:?}", assign.lhs, assign.rhs);
                log::debug!(
                    "  lhs_loc = {:?}, rhs_loc = {:?}",
                    maybe_lhs_loc,
                    maybe_rhs_loc
                );

                if let (Some(lhs_loc), Some(rhs_loc)) = (maybe_lhs_loc, maybe_rhs_loc) {
                    log::debug!("  EMIT: ${} = ${}", lhs_loc, rhs_loc);
                    if let Pattern::Deref(_) = &assign.lhs.value {
                        ctx.push(lir::Store::new(
                            lir::Variable::Local(lhs_loc),
                            lir::Atom::new(lir::Variable::Local(rhs_loc)).into(),
                            lir::Size::zero(),
                        ))
                    } else {
                        ctx.push(lir::Inst::SetLocal(
                            lhs_loc.into(),
                            lir::Atom::new(lir::Variable::Local(rhs_loc)).into(),
                        ));
                    }
                } else {
                    log::debug!("  SKIP assign: lhs or rhs None (unit?)");
                }
                lir::Value::Empty
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
                let callee_scheme = tcx.ty_of(call.callee.id);
                let mut fn_ty = tcx.instantiate_scheme(callee_scheme.clone());
                log::debug!(
                    "call: callee id={:#x} function type = {}",
                    call.callee.id,
                    fn_ty
                );

                let mut arg_exprs: Vec<(&Node<Expr>, TyScheme)> = Vec::new();
                let is_method_call = matches!(&call.callee.value, Expr::Dot(_));
                let base = if let Expr::Dot(dot) = &call.callee.value {
                    let self_ty = tcx.instantiate_scheme(tcx.ty_of(dot.lhs.id));
                    arg_exprs.push((dot.lhs.as_ref(), self_ty));
                    Some(dot.rhs.path.clone())
                } else {
                    call.callee.path()
                };

                for arg in call.args.items.iter() {
                    arg_exprs.push((arg, ctx.ty_of(tcx, arg.id)));
                }

                let mut arg_tys = arg_exprs
                    .iter()
                    .map(|(_, ty)| ty.clone())
                    .collect::<Vec<_>>();
                let original_poly_ty = tcx.get_poly_ty(call.callee.id).cloned();
                if let Some(original_poly_ty) = &original_poly_ty {
                    log::debug!("[Call::lir_gen] original_poly_ty = {}", original_poly_ty);
                } else {
                    log::debug!("[Call::lir_gen] original_poly_ty is None");
                }
                let mut instantiated_poly_ty = original_poly_ty
                    .clone()
                    .map(|ty| tcx.instantiate_scheme(ty));
                if let Some(instantiated_poly_ty) = &instantiated_poly_ty {
                    log::debug!(
                        "[Call::lir_gen] instantiated_poly_ty = {}",
                        instantiated_poly_ty
                    );
                } else {
                    log::debug!("[Call::lir_gen] instantiated_poly_ty is None");
                }
                let subst =
                    fn_ty.instantiate_fn_with_args(instantiated_poly_ty.as_mut(), &mut arg_tys);
                log::debug!(
                    "call: subst = {}, fn_ty after = {}, args={}",
                    subst,
                    fn_ty,
                    arg_tys
                        .iter()
                        .map(|ty| ty.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                for (idx, (_, ty)) in arg_exprs.iter_mut().enumerate() {
                    *ty = arg_tys[idx].clone();
                }

                // Snapshot instantiated parameter types of the callee after substitution.
                let param_monos = match fn_ty.mono().clone() {
                    Ty::Func(params, _) => params,
                    _ => Vec::new(),
                };

                let (fn_name, recv_mode) = base
                    .map(|mut func_fqn| {
                        if let Some(resolved) = tcx.call_resolution(call.call_resolution_id()) {
                            log::debug!("resolved call: {} -> {}", func_fqn, resolved);
                            func_fqn = resolved;
                        }
                        log::debug!("func_fqn = {}", func_fqn);
                        if !subst.is_empty() {
                            func_fqn.apply_subst(&subst);
                        }

                        log::debug!("traits: {:?}", tcx.traits().keys());
                        let norm_func_fqn = func_fqn.with_names_only();
                        let trait_fqn = tcx.resolve_trait_from_path(&norm_func_fqn);
                        let field = trait_fqn.and_then(|trait_fqn| {
                            tcx.get_trait_field(&trait_fqn, &func_fqn.name().unwrap())
                        });

                        log::debug!("[Call::lir_gen] field={:?}", field);

                        match (instantiated_poly_ty.as_ref(), field) {
                            (Some(inst_ty), Some(field)) => {
                                let trait_fn_ty = &field.ty;
                                log::debug!("inst_ty: {}", inst_ty);
                                log::debug!("fn_ty: {}", trait_fn_ty);
                                let (_, trait_subst) = mgu(trait_fn_ty.mono(), inst_ty.mono())
                                    .ok()
                                    .unwrap_or_default();
                                log::debug!("subst: {}", trait_subst);
                                func_fqn.apply_subst(&trait_subst);
                                (func_fqn, field.recv_mode)
                            }
                            (None, Some(field)) => (func_fqn, field.recv_mode),
                            _ => (func_fqn, ReceiverMode::None),
                        }
                    })
                    .map(|(base, recv_mode)| {
                        log::debug!("base_name: {}", base);
                        let fqn = if ctx.is_extern(&base) {
                            ctx.extern_link_name(&base).unwrap_or(base)
                        } else {
                            match &instantiated_poly_ty {
                                Some(poly_ty) if fn_ty.is_polymorphic() => {
                                    sema::fn_name(&base, poly_ty)
                                }
                                _ => sema::fn_name(&base, &fn_ty),
                            }
                        };
                        (fqn, recv_mode)
                    })
                    .unzip();

                let mut call_args: Vec<lir::Variable> = Vec::new();
                let recv_mode = recv_mode.unwrap_or_default();
                for (idx, (expr, expr_ty_scheme)) in arg_exprs.into_iter().enumerate() {
                    log::debug!(
                        "call arg[{}] id={:#x} ty = {} expr = {:?}",
                        idx,
                        expr.id,
                        ctx.ty_of(tcx, expr.id),
                        expr
                    );

                    let value = expr.lir_gen(ctx, tcx)?;

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

                            match recv_mode {
                                ReceiverMode::Ptr => {
                                    // auto-&: param is *T, expr is T
                                    if let Ty::Ref(inner) = param_mono {
                                        if **inner == expr_mono {
                                            // Ensure the receiver value lives in a local with its
                                            // original (by-value) type.
                                            let val_loc = ctx
                                                .get_or_set_local(value, expr_ty_scheme.clone())
                                                .unwrap();

                                            // Take the address of that local (no field offset).
                                            let lea = lir::Lea::new(
                                                lir::Variable::Local(val_loc),
                                                lir::LeaOffset::zero(),
                                            );

                                            // Store the resulting pointer in a local of the
                                            // parameter's pointer type.
                                            let ptr_scheme =
                                                TyScheme::from_mono(param_mono.clone());
                                            if let Some(ptr_loc) =
                                                ctx.get_or_set_local(lea.into(), ptr_scheme)
                                            {
                                                call_args.push(lir::Variable::Local(ptr_loc));
                                            } else {
                                                call_args.push(lir::Variable::Unit);
                                            }

                                            continue;
                                        }
                                    }
                                }
                                ReceiverMode::Value => {
                                    // auto-*: param is T, expr is *T
                                    if !matches!(param_mono, Ty::Ref(_))
                                        && matches!(expr_mono, Ty::Ref(inner) if *inner == *param_mono)
                                    {
                                        let val_loc = ctx
                                            .get_or_set_local(value, expr_ty_scheme.clone())
                                            .unwrap();
                                        let load = lir::Load::new(
                                            lir::Variable::Local(val_loc),
                                            lir::Size::zero(),
                                        );
                                        let val_scheme = TyScheme::from_mono(param_mono.clone());
                                        let loaded_loc =
                                            ctx.get_or_set_local(load.into(), val_scheme).unwrap();
                                        call_args.push(lir::Variable::Local(loaded_loc));
                                        continue;
                                    }
                                }
                                ReceiverMode::None => {
                                    // static method: no special receiver handling
                                }
                            }
                        }
                    }

                    // Default case: treat the argument as having the callee's
                    // parameter type when available; otherwise, fall back to
                    // the expression's own type.
                    let ty_for_local = if let Some(param_mono) = param_monos.get(idx) {
                        TyScheme::from_mono(param_mono.clone())
                    } else {
                        ctx.ty_of(tcx, expr.id)
                    };

                    if let Some(loc) = ctx.get_or_set_local(value, ty_for_local) {
                        call_args.push(lir::Variable::Local(loc));
                    } else {
                        call_args.push(lir::Variable::Unit);
                    }
                }

                let mut call_subst = subst.clone();
                if let (Some(orig_poly), Some(inst_poly)) =
                    (original_poly_ty.as_ref(), instantiated_poly_ty.as_ref())
                {
                    if let Ok((_, poly_subst)) = mgu(orig_poly.mono(), inst_poly.mono()) {
                        call_subst.union(poly_subst);
                    }
                }

                let mut val = if let Some(fn_name) = fn_name {
                    log::debug!("add sym: {}", fn_name);
                    log::debug!("poly_ty: {:?}", instantiated_poly_ty);
                    ctx.add_sym(fn_name.clone());
                    lir::Call::new(
                        fn_name,
                        call_args,
                        fn_ty.clone(),
                        original_poly_ty.clone(),
                        call_subst.clone(),
                    )
                } else {
                    let val = call.callee.lir_gen(ctx, tcx)?;
                    let fun_loc = ctx.get_or_set_local(val, fn_ty.clone()).unwrap();
                    lir::Call::new_ref(
                        fun_loc,
                        call_args,
                        fn_ty.clone(),
                        original_poly_ty.clone(),
                        call_subst,
                    )
                };

                val.source = Some(ctx.srcmap.get(self));
                val.into()
            }
            Expr::BinOp(binop) => {
                let fn_ty = ctx.ty_of(tcx, binop.op.id);
                let name = binop.op.to_string();
                let (mut func_fqn, trait_fqn) = tcx.lookup_infix_op(&name).cloned().unwrap();
                log::debug!("fn_ty: {}", fn_ty);
                log::debug!("trait_fqn: {}", trait_fqn);
                log::debug!("func_fqn: {}", func_fqn);

                ctx.call_from_op(
                    &mut func_fqn,
                    &trait_fqn,
                    &binop.op,
                    &[&binop.lhs, &binop.rhs],
                    &fn_ty,
                    tcx,
                )?
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
            Expr::Closure(_) => todo!("lir_gen: Expr::Closure: {}", self.value),
            Expr::DefaultValue(_) => todo!("lir_gen: Expr::DefaultValue: {}", self.value),
            Expr::For(_) => todo!("lir_gen: Expr::For: {}", self.value),
            Expr::If(if_ex) => {
                log::debug!("type of: {}", ty);

                // Optional binding for `if some(name) = expr { ... }`:
                // we record the payload local here so we can bind the inner
                // name in the then-branch.
                let mut some_binding: Option<(String, usize)> = None;

                let (cond_label, cond_loc) = ctx.with_new_block(|ctx| {
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
                                if let Some(name) = extract_some_binding_name(&inner_pat.value) {
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
                                        some_binding = Some((name.to_string(), payload_loc));
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
                let (then_label, then_val) = ctx.with_new_block(|ctx| {
                    // Install the binding for `some(name)` in the then-branch
                    // so that references to `name` see the payload local.
                    if let Some((ref name, payload_loc)) = some_binding {
                        ctx.set_var(name.clone(), payload_loc);
                    }
                    RayResult::Ok(if_ex.then.lir_gen(ctx, tcx)?)
                });

                let then_val = then_val?;
                let then_has_value = !matches!(then_val, lir::Value::Empty);
                let (else_label, else_val) = ctx.with_new_block(|ctx| {
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
                    ctx.with_block(then_label, |ctx| {
                        ctx.push(lir::Inst::SetLocal(if_loc.into(), then_val));
                    });

                    if let Some(else_val) = else_val? {
                        ctx.with_block(else_label, |ctx| {
                            ctx.push(lir::Inst::SetLocal(if_loc.into(), else_val));
                        });
                    }

                    Some(if_loc)
                } else {
                    // Statement `if`: emit side-effecting instructions from both
                    // branches, but do not produce a value.
                    ctx.with_block(then_label, |ctx| {
                        if let Some(i) = then_val.to_inst() {
                            ctx.push(i);
                        }
                    });
                    if let Some(ev) = else_val? {
                        ctx.with_block(else_label, |ctx| {
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
                ctx.with_block(then_label, |ctx| ctx.goto(end_label));
                ctx.with_block(else_label, |ctx| ctx.goto(end_label));

                // use the end block for the next instructions
                ctx.use_block(end_label);
                ctx.block()
                    .markers_mut()
                    .push(lir::ControlMarker::End(cond_label));

                if_loc
                    .map(|l| lir::Atom::Variable(lir::Variable::Local(l)).into())
                    .unwrap_or_default()
            }
            Expr::Index(_) => todo!("lir_gen: Expr::Index: {}", self.value),
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
            Expr::Sequence(_) => todo!("lir_gen: Expr::Sequence: {}", self.value),
            Expr::Type(ty) => lir::Value::Type(ty.clone_value()),
            Expr::UnaryOp(unop) => unop.lir_gen(ctx, tcx)?,
            Expr::Unsafe(_) => todo!("lir_gen: Expr::Unsafe: {}", self.value),
            Expr::While(while_stmt) => {
                let cond_label = ctx.new_block();
                let body_label = ctx.new_block();
                let end_label = ctx.new_block();

                let prev_control = ctx.control_block;
                ctx.control_block = Some(end_label);

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

                ctx.use_block(end_label);
                ctx.block()
                    .markers_mut()
                    .push(lir::ControlMarker::End(cond_label));

                ctx.control_block = prev_control;

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
                ctx.push(lir::Inst::SetLocal(
                    is_some_loc.into(),
                    lir::Atom::BoolConst(true).into(),
                ));
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
                    for func in funcs {
                        let node = func.as_ref();
                        let ty = tcx
                            .get_poly_ty(node.id)
                            .cloned()
                            .unwrap_or_else(|| ctx.ty_of(tcx, func.id));
                        (&node, &ty).lir_gen(ctx, tcx)?;
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
                        let ty = ctx.ty_of(tcx, self.id);
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

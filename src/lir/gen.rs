use std::{cell::RefCell, collections::HashMap, ops::Deref, rc::Rc};

use top::{mgu, solver::SolveResult, ForAll, Subst, Substitutable};

use crate::{
    ast::{
        self,
        asm::{AsmOp, AsmOperand},
        token::IntegerBase,
        CurlyElement, Decl, Expr, Literal, Modifier, Module, Node, Path, Pattern, RangeLimits,
        UnaryOp,
    },
    errors::RayResult,
    lir, sema,
    typing::{
        info::TypeSystemInfo,
        ty::{SigmaTy, Ty, TyScheme, TyVar},
        TyCtx,
    },
};

pub const START_FUNCTION: &'static str = "_start";
pub const RAY_MAIN_FUNCTION: &'static str = "_ray_main";

impl lir::Program {
    pub fn gen(
        module: &Module<(), Decl>,
        solution: &SolveResult<TypeSystemInfo, Ty, TyVar>,
        tcx: &TyCtx,
        libs: Vec<lir::Program>,
    ) -> RayResult<lir::Program> {
        let path = module.path.clone();
        let prog = Rc::new(RefCell::new(lir::Program::new(path)));
        let start_idx = {
            let mut ctx = GenCtx::new(Rc::clone(&prog), solution.subst.clone());
            module.decls.lir_gen(&mut ctx, tcx)?;

            if !module.is_lib {
                let mut main_symbols = lir::SymbolSet::new();
                let main_path = prog.borrow().main_path();
                log::debug!("main function path: {}", main_path);

                ctx.with_builder(lir::Builder::new());
                ctx.with_new_block(|ctx| {
                    // call all the main functions from the libs first
                    let mut main_funcs = libs.iter().map(|l| l.main_path()).collect::<Vec<_>>();

                    // then call _this_ module's main function
                    main_funcs.push(main_path.clone());

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
        let main_path = self.main_path();
        let mut i = 0;
        while i < self.funcs.len() {
            let f = &self.funcs[i];
            if f.name == START_FUNCTION {
                self.start_idx = i as i64;
            } else if f.name == main_path {
                self.user_main_idx = i as i64;
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
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<T>;
}

impl<T, U> LirGen<Vec<U>> for Vec<T>
where
    T: LirGen<U>,
{
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<Vec<U>> {
        self.iter()
            .map(|t| t.lir_gen(ctx, tcx))
            .collect::<RayResult<Vec<_>>>()
    }
}

#[derive(Clone, Debug)]
pub struct GenCtx {
    prog: Rc<RefCell<lir::Program>>,
    builder: Option<lir::Builder>,
    fn_idx: HashMap<String, usize>,
    data_idx: HashMap<Vec<u8>, usize>,
    global_idx: HashMap<String, usize>,
    inst_map: Subst<TyVar, Ty>,
}

impl std::ops::Deref for GenCtx {
    type Target = lir::Builder;

    fn deref(&self) -> &Self::Target {
        self.builder.as_ref().unwrap()
    }
}

impl std::ops::DerefMut for GenCtx {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.builder.as_mut().unwrap()
    }
}

impl GenCtx {
    fn new(prog: Rc<RefCell<lir::Program>>, inst_map: Subst<TyVar, Ty>) -> GenCtx {
        // let scope = prog.borrow().module_path.clone();
        GenCtx {
            prog,
            builder: None,
            fn_idx: HashMap::new(),
            data_idx: HashMap::new(),
            global_idx: HashMap::new(),
            inst_map,
        }
    }

    fn with_builder(&mut self, builder: lir::Builder) {
        self.builder = Some(builder);
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
        name: Path,
        ty: TyScheme,
        is_mutable: bool,
        modifiers: Vec<Modifier>,
        src: Option<String>,
    ) {
        let idx = self.prog.borrow().externs.len();
        let mut prog = self.prog.borrow_mut();
        prog.extern_map.insert(name.clone(), idx);
        prog.externs.push(lir::Extern {
            name,
            ty,
            is_mutable,
            modifiers,
            src,
        });
    }

    fn is_extern(&self, name: &Path) -> bool {
        let prog = self.prog.borrow();
        prog.extern_map.contains_key(name)
    }

    fn new_global(&mut self, name: &Path, init_value: lir::Value, ty: TyScheme, mutable: bool) {
        let mut prog = self.prog.borrow_mut();
        let idx = prog.globals.len();
        let name = name.to_string();
        self.global_idx.insert(name.clone(), idx);
        prog.globals.push(lir::Global {
            idx,
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
        let idx = prog.data.len();
        self.data_idx.insert(value.clone(), idx);

        let name = format!(".data.{}", idx);
        prog.data.push(lir::Data::new(idx, name, value));
        idx
    }

    fn get_or_set_local(&mut self, value: lir::Value, ty: TyScheme) -> Option<usize> {
        if ty.is_unit() {
            if let Some(i) = value.to_inst() {
                self.push(i);
            }
            None
        } else if let Some(idx) = value.local() {
            Some(idx)
        } else {
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
        let poly_ty = tcx.get_poly_ty(op).unwrap();
        let subst = mgu(poly_ty.mono(), fn_ty.mono())
            .ok()
            .map(|(_, s)| s)
            .unwrap_or_default();
        log::debug!("subst: {}", subst);
        func_fqn.apply_subst(&subst);
        log::debug!("func_fqn: {}", func_fqn);

        let base = trait_fqn.merge(&func_fqn);

        log::debug!("base_name: {}", base);
        let fn_name = if !self.is_extern(&base) {
            if fn_ty.is_polymorphic() {
                sema::fn_name(&base, &poly_ty)
            } else {
                sema::fn_name(&base, fn_ty)
            }
        } else {
            base
        };

        let mut call_args: Vec<lir::Variable> = vec![];
        for arg in args {
            let arg_ty = tcx.ty_of(arg.id);
            let arg_val = arg.lir_gen(self, tcx)?;

            if let Some(arg_loc) = self.get_or_set_local(arg_val, arg_ty) {
                call_args.push(lir::Variable::Local(arg_loc));
            } else {
                call_args.push(lir::Variable::Unit)
            }
        }
        log::debug!("add sym: {}", fn_name);
        self.add_sym(fn_name.clone());
        Ok(lir::Call::new(fn_name, call_args, fn_ty.clone(), Some(poly_ty.clone())).into())
    }
}

pub type GenResult = lir::Value;

impl LirGen<GenResult> for (&Expr, &TyScheme) {
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        let &(ex, ty) = self;
        Ok(match ex {
            Expr::Path(v) => (v, ty).lir_gen(ctx, tcx)?,
            Expr::Name(n) => (&n.path, ty).lir_gen(ctx, tcx)?,
            Expr::Pattern(p) => (p, ty).lir_gen(ctx, tcx)?,
            Expr::Literal(lit) => (lit, ty).lir_gen(ctx, tcx)?,
            Expr::Paren(ex) | Expr::TypeAnnotated(ex, _) => ex.lir_gen(ctx, tcx)?,
            Expr::New(new) => {
                let count = match &new.count {
                    Some(c) => {
                        let ty = tcx.ty_of(c.id);
                        let value = c.lir_gen(ctx, tcx)?;
                        lir::Variable::Local(ctx.get_or_set_local(value, ty).unwrap()).into()
                    }
                    _ => lir::Atom::uptr(1),
                };
                lir::Malloc::new(new.ty.deref().deref().clone().into(), count)
            }
            Expr::Cast(c) => {
                let src = c.lhs.lir_gen(ctx, tcx)?;
                let lhs_ty = tcx.ty_of(c.lhs.id);
                let loc = ctx.get_or_set_local(src, lhs_ty).unwrap();
                lir::Cast::new(lir::Variable::Local(loc), c.ty.deref().clone())
            }
            Expr::Range(range) => {
                // create a `range` struct
                //  - start: T
                //  - end: T
                //  - inclusive: bool
                let loc = ctx.local(ty.clone());
                let el_ty = tcx.ty_of(range.start.id);
                let ptr = lir::Malloc::new(ty.clone(), lir::Atom::uptr(1));
                ctx.push(lir::Inst::SetLocal(loc.into(), ptr.into()));

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
            Expr::Tuple(tuple) => {
                let tys = variant!(ty.mono(), if Ty::Tuple(tys));

                // create a new local for the tuple and then make an allocation
                let tuple_loc = ctx.local(ty.clone());
                let size = ty.mono().size_of();
                if !size.is_zero() {
                    let ptr = lir::Malloc::new(ty.clone(), lir::Atom::uptr(1));
                    ctx.push(lir::Inst::SetLocal(tuple_loc.into(), ptr.into()));

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
                                size,
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
                let el_ty = ty.mono().get_ty_param_at(0);
                let el_size = el_ty.size_of();
                let values_loc = ctx.local(el_ty.clone().into());
                let values_ptr = lir::Malloc::new(el_ty.clone().into(), lir::Atom::uptr(capacity));
                ctx.push(lir::Inst::SetLocal(values_loc.into(), values_ptr.into()));

                let mut offset = lir::Size::zero();
                for item in list.items.iter() {
                    let item_val = item.lir_gen(ctx, tcx)?;
                    if let Some(item_loc) = ctx.get_or_set_local(item_val, tcx.ty_of(item.id)) {
                        ctx.push(lir::Store::new(
                            lir::Variable::Local(values_loc),
                            lir::Variable::Local(item_loc).into(),
                            offset,
                            el_size,
                        ));
                    }

                    offset += el_size;
                }

                // allocate space for the list struct
                //   - values ptr: *'a
                //   - len: uint
                //   - capacity: uint
                let list_loc = ctx.local(ty.clone());
                let list_ptr = lir::Malloc::new(ty.clone(), lir::Atom::uptr(1));
                ctx.push(lir::Inst::SetLocal(list_loc.into(), list_ptr.into()));

                // store the values ptr
                ctx.push(lir::SetField::new(
                    lir::Variable::Local(list_loc),
                    str!("values"),
                    lir::Variable::Local(values_loc).into(),
                ));

                // store the length
                ctx.push(lir::SetField::new(
                    lir::Variable::Local(list_loc),
                    str!("length"),
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
            Expr::Asm(asm) => {
                fn convert_var(operand: &AsmOperand, ty: Ty, ctx: &mut GenCtx) -> lir::Variable {
                    match operand {
                        AsmOperand::Var(name) => {
                            let loc = ctx.get_var(name).copied().unwrap_or_else(|| {
                                // variable is not defined in the current block, so create a ref
                                let idx = ctx.local(ty.into());
                                ctx.set_var(name.clone(), idx);
                                idx
                            });
                            lir::Variable::Local(loc)
                        }
                        AsmOperand::Int(_) => panic!("not a variable: {:?}", operand),
                    }
                }

                fn convert_operand(operand: &AsmOperand, ty: Ty, ctx: &mut GenCtx) -> lir::Atom {
                    match operand {
                        AsmOperand::Var(_) => convert_var(operand, ty, ctx).into(),
                        AsmOperand::Int(i) => lir::Atom::uptr(*i),
                    }
                }

                // TODO: This is a terrible way to hanlde this
                let mut binops = asm
                    .inst
                    .iter()
                    .flat_map(|(op, rands)| match op {
                        AsmOp::MemCopy => {
                            let dst = convert_var(&rands[0], Ty::uint(), ctx);
                            let src = convert_var(&rands[1], Ty::uint(), ctx);
                            let size = convert_operand(&rands[2], Ty::uint(), ctx);
                            ctx.push(lir::Inst::MemCopy(dst, src, size));
                            None
                        }

                        _ => {
                            let mut binop = lir::BasicOp::from(*op);
                            binop.operands.extend(rands.iter().map(|operand| {
                                convert_operand(operand, ty.clone().into_mono(), ctx)
                            }));
                            Some(lir::Value::BasicOp(binop))
                        }
                    })
                    .collect::<Vec<_>>();

                if let Some(value) = binops.pop() {
                    let idx = ctx.get_or_set_local(value, ty.clone()).unwrap();
                    lir::Value::new(lir::Variable::Local(idx))
                } else {
                    lir::Value::Empty
                }
            }
            Expr::Curly(curly) => {
                let loc = ctx.local(ty.clone());
                let mut field_insts = vec![];
                for field in curly.elements.iter() {
                    let (name, field_value) =
                        variant!(&field.value, if CurlyElement::Labeled(x, y));
                    let field_ty = tcx.ty_of(field.id);
                    let val = field_value.lir_gen(ctx, tcx)?;
                    field_insts.push((val, name.clone(), field_ty));
                }

                ctx.push(lir::Inst::SetLocal(
                    loc.into(),
                    lir::Malloc::new(ty.clone(), lir::Atom::uptr(1)).into(),
                ));

                for (val, name, ty) in field_insts {
                    if let Some(field_loc) = ctx.get_or_set_local(val, ty) {
                        ctx.push(lir::SetField::new(
                            lir::Variable::Local(loc),
                            name.to_string(),
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
            Expr::Assign(assign) => {
                // get types of both sides
                let lhs_ty = tcx.ty_of(assign.lhs.id);
                let rhs_ty = tcx.ty_of(assign.rhs.id);

                let rhs_val = assign.rhs.lir_gen(ctx, tcx)?;
                let lhs_val = (&assign.lhs.value, &lhs_ty).lir_gen(ctx, tcx)?;
                let maybe_lhs_loc = ctx.get_or_set_local(lhs_val, lhs_ty.clone());
                let maybe_rhs_loc = ctx.get_or_set_local(rhs_val, rhs_ty);

                if let (Some(lhs_loc), Some(rhs_loc)) = (maybe_lhs_loc, maybe_rhs_loc) {
                    if let Pattern::Deref(_) = &assign.lhs.value {
                        let rhs_ty = tcx.ty_of(assign.rhs.id);
                        ctx.push(lir::Store::new(
                            lir::Variable::Local(lhs_loc),
                            lir::Atom::new(lir::Variable::Local(rhs_loc)).into(),
                            lir::Size::zero(),
                            rhs_ty.mono().size_of(),
                        ))
                    } else {
                        ctx.push(lir::Inst::SetLocal(
                            lhs_loc.into(),
                            lir::Atom::new(lir::Variable::Local(rhs_loc)).into(),
                        ));
                    }
                }
                lir::Value::Empty
            }
            Expr::Func(_) => todo!(),
            Expr::Dot(dot) => {
                let lhs_val = dot.lhs.lir_gen(ctx, tcx)?;
                let lhs_ty = tcx.ty_of(dot.lhs.id);
                let lhs_loc = ctx.get_or_set_local(lhs_val, lhs_ty.clone()).unwrap();

                lir::GetField {
                    src: lir::Variable::Local(lhs_loc),
                    field: dot.rhs.path.to_string(),
                }
                .into()
            }
            Expr::Call(call) => {
                let mut call_args: Vec<lir::Variable> = vec![];
                let fn_ty = tcx.ty_of(call.callee.id);
                log::debug!("call: function type = {}", fn_ty);

                let base = if let Expr::Dot(dot) = &call.callee.value {
                    let self_ty = tcx.ty_of(dot.lhs.id);
                    let self_val = dot.lhs.lir_gen(ctx, tcx)?;
                    let self_loc = ctx.get_or_set_local(self_val, self_ty).unwrap();
                    call_args.push(lir::Variable::Local(self_loc));
                    Some(dot.rhs.path.clone())
                } else {
                    call.callee.path()
                };

                let mut poly_ty = tcx.get_poly_ty(&call.callee).cloned();
                if let Some(poly_ty) = &mut poly_ty {
                    // create a substitution that maps the type parameters to the type arguments
                    let (_, subst) = mgu(poly_ty.mono(), fn_ty.mono()).ok().unwrap_or_default();
                    log::debug!("subst = {}", subst);
                    // remove any non-variable types from the substitution
                    let subst = subst.into_iter().filter(|(_, v)| v.is_tyvar()).collect();

                    // we do `apply_subst_all` here because we want to substitute the
                    // type parameters which are ignored by a call to `apply_subst`
                    poly_ty.apply_subst_all(&subst);
                    log::debug!("poly_ty = {:?}", poly_ty);
                } else {
                    log::debug!("poly_ty = None");
                }

                let fn_name = base
                    .map(|base| {
                        let fn_name = base.to_string();
                        log::debug!("fn_name = {}", fn_name);
                        if let Some((mut func_fqn, trait_fqn)) =
                            tcx.lookup_fqn_with_trait(&fn_name).cloned()
                        {
                            log::debug!("func_fqn: {}", func_fqn);
                            if let Some((poly_ty, trait_fn_ty)) =
                                poly_ty.as_ref().and_then(|poly_ty| {
                                    trait_fqn
                                        .and_then(|trait_fqn| {
                                            tcx.get_trait_fn(&trait_fqn, &fn_name)
                                        })
                                        .map(|fn_ty| (poly_ty, fn_ty))
                                })
                            {
                                log::debug!("poly_ty: {}", poly_ty);
                                log::debug!("fn_ty: {}", trait_fn_ty);
                                let (_, subst) = mgu(trait_fn_ty.mono(), poly_ty.mono())
                                    .ok()
                                    .unwrap_or_default();
                                log::debug!("subst: {}", subst);
                                func_fqn.apply_subst(&subst);
                            }

                            func_fqn
                        } else {
                            base
                        }
                    })
                    .map(|base| {
                        log::debug!("base_name: {}", base);
                        if !ctx.is_extern(&base) {
                            match &poly_ty {
                                Some(poly_ty) if fn_ty.is_polymorphic() => {
                                    sema::fn_name(&base, poly_ty)
                                }
                                _ => sema::fn_name(&base, &fn_ty),
                            }
                        } else {
                            base
                        }
                    });

                for arg in call.args.items.iter() {
                    let arg_ty = tcx.ty_of(arg.id);
                    let arg_val = arg.lir_gen(ctx, tcx)?;

                    if let Some(arg_loc) = ctx.get_or_set_local(arg_val, arg_ty) {
                        call_args.push(lir::Variable::Local(arg_loc));
                    } else {
                        call_args.push(lir::Variable::Unit)
                    }
                }

                let val = if let Some(fn_name) = fn_name {
                    log::debug!("add sym: {}", fn_name);
                    log::debug!("poly_ty: {:?}", poly_ty);
                    ctx.add_sym(fn_name.clone());
                    lir::Call::new(fn_name, call_args, fn_ty.clone(), poly_ty)
                } else {
                    let val = call.callee.lir_gen(ctx, tcx)?;
                    let fun_loc = ctx.get_or_set_local(val, fn_ty.clone()).unwrap();
                    lir::Call::new_ref(fun_loc, call_args, fn_ty.clone(), poly_ty)
                };

                val.into()
            }
            Expr::BinOp(binop) => {
                let fn_ty = tcx.ty_of(binop.op.id);
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
            Expr::Closure(_) => todo!("lir_gen: Expr::Closure: {}", ex),
            Expr::DefaultValue(_) => todo!("lir_gen: Expr::DefaultValue: {}", ex),
            Expr::For(_) => todo!("lir_gen: Expr::For: {}", ex),
            Expr::If(if_ex) => {
                log::debug!("type of: {}", ty);

                let (cond_label, cond_loc) = ctx.with_new_block(|ctx| {
                    ctx.block().markers_mut().push(lir::ControlMarker::If);
                    let cond_val = if_ex.cond.lir_gen(ctx, tcx)?;
                    RayResult::Ok(ctx.get_or_set_local(cond_val, Ty::bool().into()).unwrap())
                });

                // in the _current_ block, goto the condition
                ctx.goto(cond_label);

                let then_ty = tcx.ty_of(if_ex.then.id);
                let (then_label, then_val) =
                    ctx.with_new_block(|ctx| RayResult::Ok(if_ex.then.lir_gen(ctx, tcx)?));

                let then_val = then_val?;
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
                let if_loc = if !then_ty.is_unit() {
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
                    ctx.with_block(then_label, |ctx| {
                        if let Some(i) = then_val.to_inst() {
                            ctx.push(i);
                        }
                    });
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
            Expr::Index(_) => todo!("lir_gen: Expr::Index: {}", ex),
            Expr::Labeled(_, _) => todo!("lir_gen: Expr::Labeled: {}", ex),
            Expr::Loop(_) => todo!("lir_gen: Expr::Loop: {}", ex),
            Expr::Return(_) => todo!("lir_gen: Expr::Return: {}", ex),
            Expr::Sequence(_) => todo!("lir_gen: Expr::Sequence: {}", ex),
            Expr::Type(_) => todo!("lir_gen: Expr::Type: {}", ex),
            Expr::UnaryOp(unop) => unop.lir_gen(ctx, tcx)?,
            Expr::Unsafe(_) => todo!("lir_gen: Expr::Unsafe: {}", ex),
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
        })
    }
}

impl LirGen<GenResult> for (&Pattern, &TyScheme) {
    fn lir_gen(&self, ctx: &mut GenCtx, _: &TyCtx) -> RayResult<GenResult> {
        let &(pat, ty) = self;
        match pat {
            Pattern::Name(name) | Pattern::Deref(name) => {
                let name = name.to_string();
                let idx = ctx.get_var(&name).copied().unwrap_or_else(|| {
                    // this variable is not referenced in the current block
                    let idx = ctx.local(ty.clone());
                    ctx.set_var(name.clone(), idx);
                    idx
                });
                Ok(lir::Value::new(lir::Variable::Local(idx)))
            }
            Pattern::Sequence(_) => todo!(),
            Pattern::Tuple(_) => todo!(),
        }
    }
}

impl LirGen<GenResult> for (&Path, &TyScheme) {
    fn lir_gen(&self, ctx: &mut GenCtx, _: &TyCtx) -> RayResult<GenResult> {
        let &(path, ty) = self;
        let name = path.to_string();
        if let Some(&global) = ctx.global_idx.get(&name) {
            return Ok(lir::Variable::Global(global).into());
        }

        let loc = ctx.get_var(&name).copied().unwrap_or_else(|| {
            // variable not defined in the current block
            let idx = ctx.local(ty.clone());
            ctx.set_var(name.clone(), idx);
            idx
        });
        Ok(lir::Variable::Local(loc).into())
    }
}

impl LirGen<GenResult> for (&Literal, &TyScheme) {
    fn lir_gen(&self, ctx: &mut GenCtx, _: &TyCtx) -> RayResult<GenResult> {
        let &(lit, _) = self;
        Ok(match lit {
            Literal::Integer {
                value,
                base,
                size,
                signed,
            } => match base {
                IntegerBase::Decimal => {
                    let size = lir::Size::bytes(size / 8);
                    lir::Value::new(if *signed {
                        let c = value.parse::<i64>()?;
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
            Literal::Float { .. } => todo!(),
            Literal::String(s) => {
                // convert the string to bytes and add a `Data` to the program
                let bytes = s.as_bytes().to_vec();
                let len = bytes.len();
                let string_size = lir::Size::bytes(len);
                let idx = ctx.data(bytes);

                // allocate a pointer to store the string bytes
                let data_loc = ctx.local(Ty::ptr(Ty::u8()).into());
                let ptr = lir::Malloc::new(Ty::u8().into(), lir::Atom::uptr(len as u64));
                ctx.push(lir::Inst::SetLocal(data_loc.into(), ptr.into()));

                // make a call to `memcpy` to copy the bytes
                ctx.push(lir::Inst::MemCopy(
                    lir::Variable::Local(data_loc), // dst
                    lir::Variable::Data(idx),       // src
                    string_size.into(),             // size
                ));

                // create a `string` struct
                //  - raw_ptr: *u8
                //  - size: usize
                let loc = ctx.local(Ty::string().into());
                let ptr = lir::Malloc::new(Ty::string().into(), lir::Atom::uptr(1));
                ctx.push(lir::Inst::SetLocal(loc.into(), ptr.into()));

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
            Literal::Nil => lir::Atom::uptr(0).into(),
        })
    }
}

impl LirGen<GenResult> for (&Node<&ast::Func>, &TyScheme) {
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        let &(func, fn_ty) = self;
        let poly_ty = tcx.get_poly_ty(func);

        ctx.with_builder(lir::Builder::new());

        ctx.with_entry_block(|ctx| {
            // add the parameters to the function
            for p in func.sig.params.iter() {
                let name = p.name().unwrap().to_string();
                let ty = tcx.ty_of(p.id);
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
            let (_, _, _, ret_ty) = fn_ty
                .try_borrow_fn()
                .expect(&format!("function type, but found {:?}", fn_ty));
            let value = if !ret_ty.is_unit() {
                let body_loc = ctx.get_or_set_local(body_val, tcx.ty_of(body.id)).unwrap();
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
            base.clone()
        };

        let mut func = Node::with_id(
            func.id,
            lir::Func::new(
                base.clone(),
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
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        let fn_ty = tcx.ty_of(self.op.id);
        let name = self.op.to_string();
        let (mut func_fqn, trait_fqn) = tcx.lookup_prefix_op(&name).cloned().unwrap();
        log::debug!("trait_fqn: {}", trait_fqn);
        log::debug!("func_fqn: {}", func_fqn);

        let (expr, ty) = (self.expr.as_ref(), tcx.ty_of(self.expr.id));

        ctx.call_from_op(&mut func_fqn, &trait_fqn, &self.op, &[expr], &fn_ty, tcx)
    }
}

impl LirGen<GenResult> for Node<Expr> {
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        let ty = tcx.ty_of(self.id);
        (&self.value, &ty).lir_gen(ctx, tcx)
    }
}

impl LirGen<GenResult> for Node<Decl> {
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        log::debug!("getting type of: {:#x}", self.id);
        match &self.value {
            Decl::Func(func) => {
                let ty = tcx.ty_of(self.id);
                let node = Node::with_id(self.id, func);
                return (&node, &ty).lir_gen(ctx, tcx);
            }
            Decl::Mutable(_) | Decl::Name(_) => {
                todo!()
            }
            Decl::Trait(tr) => {
                for func in tr.fields.iter() {
                    let func = variant!(func.deref(), if Decl::FnSig(f));
                    ctx.add_trait_member(func.path.clone());
                }
            }
            Decl::Impl(imp) => {
                if let Some(consts) = &imp.consts {
                    for const_node in consts {
                        let ty = tcx.ty_of(const_node.lhs.id);
                        let name = const_node.lhs.path().unwrap();
                        let init_value = const_node.rhs.lir_gen(ctx, tcx)?;
                        ctx.new_global(name, init_value, ty, false);
                    }
                }

                if let Some(funcs) = &imp.funcs {
                    for func in funcs {
                        let ty = tcx.ty_of(func.id);
                        let node = func.as_ref();
                        (&node, &ty).lir_gen(ctx, tcx)?;
                    }
                }
            }
            Decl::Extern(ext) => {
                let decl = ext.decl();
                let src = ext.src();
                match ext.decl() {
                    Decl::Mutable(name) | Decl::Name(name) => {
                        let is_mutable = matches!(decl, Decl::Mutable(_));
                        let ty = tcx.ty_of(name.id);
                        ctx.new_extern(name.path.clone(), ty, is_mutable, vec![], src.clone());
                    }
                    Decl::FnSig(sig) => {
                        let ty = tcx.ty_of(self.id);
                        ctx.new_extern(
                            sig.path.clone(),
                            ty,
                            false,
                            sig.modifiers.clone(),
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

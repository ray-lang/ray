use std::{
    cell::{RefCell, RefMut},
    collections::HashMap,
    rc::Rc,
};

use crate::{
    ast::{
        self,
        asm::{AsmOp, AsmOperand},
        token::IntegerBase,
        CurlyElement, Decl, Expr, Extern, Literal, Module, Node, Path, Pattern, RangeLimits,
        SourceInfo,
    },
    errors::RayResult,
    hir::HirInfo,
    lir, sema,
    typing::{solvers::Solution, traits::HasType, ty::Ty, Subst, TyCtx},
};

impl lir::Program {
    pub fn gen(
        module: &Module<Expr, Decl>,
        solution: &Solution,
        tcx: &TyCtx,
    ) -> RayResult<lir::Program> {
        let path = module.path.clone();
        let prog = Rc::new(RefCell::new(lir::Program::new(path)));
        let start_idx = {
            let mut ctx = GenCtx::new(Rc::clone(&prog), solution.inst_map.clone());
            module.decls.lir_gen(&mut ctx, tcx)?;

            // add the _start function
            let start_idx =
                ctx.new_func(Path::from("_start"), Ty::Func(vec![], Box::new(Ty::unit())));
            ctx.fx = start_idx;

            let mut start_fn = ctx.borrow_func_mut();
            start_fn.symbols.insert(Path::from("main::<():()>"));
            start_fn.body.instructions = vec![
                lir::Call::new(
                    Path::from("main::<():()>"),
                    vec![],
                    Ty::Func(vec![], Box::new(Ty::unit())),
                    None,
                )
                .into(),
                lir::Inst::Return(lir::Value::Empty).into(),
            ];

            start_idx
        };

        // take the prog out of the pointer
        let mut prog = Rc::try_unwrap(prog).unwrap().into_inner();
        prog.start_idx = start_idx as i64;
        Ok(prog)
    }

    pub fn monomorphize(&mut self) {
        let mut mr = sema::Monomorphizer::new(self);
        let mut funcs = vec![];
        for func in self.funcs.iter_mut() {
            if !func.ty.is_polymorphic() {
                funcs.extend(mr.monomorphize(func));
            }
        }

        // remove the polymorphic functions
        let mut i = 0;
        while i < self.funcs.len() {
            let f = &self.funcs[i];
            if f.name == "_start" {
                self.start_idx = i as i64;
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

#[derive(Clone, Debug)]
pub struct GenCtx {
    prog: Rc<RefCell<lir::Program>>,
    // scope: Path,
    fx: usize,
    label_idx: usize,
    fn_idx: HashMap<String, usize>,
    data_idx: HashMap<Vec<u8>, usize>,
    vars: HashMap<String, usize>,
    inst_map: Subst,
}

impl GenCtx {
    fn new(prog: Rc<RefCell<lir::Program>>, inst_map: Subst) -> GenCtx {
        // let scope = prog.borrow().module_path.clone();
        GenCtx {
            prog,
            // scope,
            fx: 0,
            label_idx: 0,
            fn_idx: HashMap::new(),
            data_idx: HashMap::new(),
            vars: HashMap::new(),
            inst_map,
        }
    }

    fn new_loc_with(
        locals: &mut Vec<lir::Local>,
        ty: Ty,
        name: Option<String>,
    ) -> (usize, lir::Size) {
        let idx = locals.len();
        let size = ty.size_of();
        let mut loc = lir::Local::new(idx, ty);
        loc.name = name;
        locals.push(loc);
        (idx, size)
    }

    fn new_loc(&mut self, ty: Ty) -> (usize, lir::Size) {
        let mut prog = self.prog.borrow_mut();
        let func = prog.funcs.get_mut(self.fx).unwrap();
        GenCtx::new_loc_with(&mut func.locals, ty, None)
    }

    fn set_loc(&mut self, loc: usize, value: lir::Value, ty: Ty, value_ty: Ty) -> Vec<lir::Inst> {
        let mut inst = vec![];
        if let Ty::Union(tys) = ty {
            // need to malloc a union
            let tag_size = lir::Size::bytes((tys.len() + 7) / 8);
            let max_size = tys.iter().map(Ty::size_of).max().unwrap_or_default();
            let size = tag_size + max_size;
            inst.push(lir::Inst::SetLocal(loc, lir::Malloc::new(size)));

            // get the tag
            let mut tag = 0;
            for (i, ty) in tys.iter().enumerate() {
                if ty == &value_ty {
                    tag = i;
                    break;
                }
            }

            // store the tag
            inst.push(lir::Store::new(
                lir::Variable::Local(loc),
                lir::Atom::UintConst(tag as u64, tag_size).into(),
                lir::Size::zero(),
                tag_size,
            ));

            // store the value
            let value_size = value_ty.size_of();
            inst.push(lir::Store::new(
                lir::Variable::Local(loc),
                value,
                tag_size,
                value_size,
            ));
        } else {
            inst.push(lir::Inst::SetLocal(loc, value));
        };

        inst
    }

    fn new_param(&mut self, name: String, ty: Ty) -> (usize, lir::Size) {
        let mut prog = self.prog.borrow_mut();
        let func = prog.funcs.get_mut(self.fx).unwrap();
        let (idx, size) = GenCtx::new_loc_with(&mut func.locals, ty.clone(), Some(name.clone()));
        self.vars.insert(name.clone(), idx);
        func.params.push(lir::Param {
            idx,
            size,
            name,
            ty,
        });

        (idx, size)
    }

    fn new_var(&mut self, v: String, ty: Ty) -> (usize, lir::Size) {
        let (idx, size) = self.new_loc(ty);
        self.vars.insert(v, idx);
        (idx, size)
    }

    fn new_label(&mut self) -> String {
        let idx = self.label_idx;
        self.label_idx += 1;
        let mut prog = self.prog.borrow_mut();
        let func = prog.funcs.get_mut(self.fx).unwrap();
        format!("{}::__label{}", func.name, idx)
    }

    fn add_sym(&mut self, sym: Path) {
        self.borrow_func_mut().symbols.insert(sym);
    }

    fn new_func(&mut self, name: Path, ty: Ty) -> usize {
        let mut prog = self.prog.borrow_mut();
        let idx = prog.funcs.len();
        if ty.is_polymorphic() {
            prog.poly_fn_map.insert(name.clone(), idx);
        }

        prog.funcs.push(lir::Func::new(name, ty));
        idx
    }

    fn is_poly_func(&self, name: &Path) -> bool {
        let prog = self.prog.borrow();
        prog.poly_fn_map.contains_key(name)
    }

    fn borrow_func_mut(&mut self) -> RefMut<'_, lir::Func> {
        let prog = self.prog.borrow_mut();
        RefMut::map(prog, |p| p.funcs.get_mut(self.fx).unwrap())
    }

    fn new_extern(&mut self, name: Path, ty: Ty, is_mutable: bool, src: Option<String>) {
        let mut prog = self.prog.borrow_mut();
        prog.extern_set.insert(name.clone());
        prog.externs.push(lir::Extern {
            name,
            ty,
            is_mutable,
            src,
        });
    }

    fn is_extern(&self, name: &Path) -> bool {
        let prog = self.prog.borrow();
        prog.extern_set.contains(name)
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

    fn get_or_set_local(&mut self, value: lir::Value, ty: Ty, inst: &mut Vec<lir::Inst>) -> usize {
        if let lir::Value::Atom(lir::Atom::Variable(lir::Variable::Local(idx))) = value {
            idx
        } else {
            let (idx, _) = self.new_loc(ty.clone());
            inst.push(lir::Inst::SetLocal(idx, value).into());
            idx
        }
    }
}

pub type GenResult = (Vec<lir::Inst>, lir::Value);

impl LirGen<GenResult> for (&Expr, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        let &(ex, ty) = self;
        Ok(match ex {
            Expr::Path(v) => (v, ty).lir_gen(ctx, tcx)?,
            Expr::Name(n) => (&n.path, ty).lir_gen(ctx, tcx)?,
            Expr::Literal(lit) => (lit, ty).lir_gen(ctx, tcx)?,
            Expr::Cast(c) => c.lhs.lir_gen(ctx, tcx)?,
            Expr::Paren(ex) | Expr::TypeAnnotated(ex, _) => ex.lir_gen(ctx, tcx)?,
            Expr::Range(range) => {
                let mut inst = vec![];
                // create a `range` struct
                //  - start: T
                //  - end: T
                //  - inclusive: bool
                let (loc, _) = ctx.new_loc(ty.clone());
                let el_ty = tcx.ty_of(range.start.id);
                let el_size = el_ty.size_of();
                let size = (el_size * 2) + lir::Size::bytes(1);
                let ptr = lir::Malloc::new(size);
                inst.push(lir::Inst::SetLocal(loc, ptr.into()));

                // store the start value
                let (start_inst, start_val) = range.start.lir_gen(ctx, tcx)?;
                inst.extend(start_inst);
                let start_loc = ctx.get_or_set_local(start_val, el_ty.clone(), &mut inst);
                inst.push(lir::Store::new(
                    lir::Variable::Local(loc),
                    lir::Variable::Local(start_loc).into(),
                    lir::Size::zero(),
                    el_size,
                ));

                // store the end value
                let (end_inst, end_val) = range.end.lir_gen(ctx, tcx)?;
                inst.extend(end_inst);
                let end_loc = ctx.get_or_set_local(end_val, el_ty.clone(), &mut inst);
                inst.push(lir::Store::new(
                    lir::Variable::Local(loc),
                    lir::Variable::Local(end_loc).into(),
                    el_size,
                    lir::Size::ptr(),
                ));

                // store the inclusive flag
                let (bool_loc, bool_size) = ctx.new_loc(Ty::bool());
                inst.push(lir::Inst::SetLocal(
                    bool_loc,
                    lir::Atom::UintConst(
                        if matches!(range.limits, RangeLimits::Inclusive) {
                            1
                        } else {
                            0
                        },
                        bool_size,
                    )
                    .into(),
                ));
                inst.push(lir::Store::new(
                    lir::Variable::Local(loc),
                    lir::Variable::Local(bool_loc).into(),
                    el_size * 2,
                    bool_size,
                ));

                (inst, lir::Atom::new(lir::Variable::Local(loc)).into())
            }
            Expr::Tuple(tuple) => {
                let mut inst = vec![];
                let tys = variant!(ty, if Ty::Tuple(tys));

                // create a new local for the tuple and then make an allocation
                let (tuple_loc, size) = ctx.new_loc(ty.clone());
                let value = if !size.is_zero() {
                    let ptr = lir::Malloc::new(size);
                    inst.push(lir::Inst::SetLocal(tuple_loc, ptr.into()));

                    // for each element of the tuple, store it on the stack
                    let mut offset = lir::Size::zero();
                    for (el, ty) in tuple.seq.items.iter().zip(tys.iter().cloned()) {
                        // generate the lir for the element
                        let (el_inst, val) = el.lir_gen(ctx, tcx)?;
                        let size = ty.size_of();
                        inst.extend(el_inst);
                        let el_loc = ctx.get_or_set_local(val, ty, &mut inst);

                        // store the element on the stack
                        inst.push(lir::Store::new(
                            lir::Variable::Local(tuple_loc),
                            lir::Atom::new(lir::Variable::Local(el_loc)).into(),
                            offset,
                            size,
                        ));

                        offset += size;
                    }

                    lir::Value::new(lir::Variable::Local(tuple_loc))
                } else {
                    lir::Value::new(lir::Atom::NilConst)
                };

                (inst, value)
            }
            Expr::List(list) => {
                let mut inst = vec![];
                let item_count = list.items.len();
                let capacity = item_count * 3;

                // allocate memory for the values
                let el_ty = ty.get_ty_param_at(0);
                let (values_loc, el_size) = ctx.new_loc(el_ty.clone());
                let values_ptr = lir::Malloc::new(el_size * capacity);
                inst.push(lir::Inst::SetLocal(values_loc, values_ptr.into()));

                let mut offset = lir::Size::zero();
                for item in list.items.iter() {
                    let (item_inst, item_val) = item.lir_gen(ctx, tcx)?;
                    inst.extend(item_inst);
                    let item_loc = ctx.get_or_set_local(item_val, tcx.ty_of(item.id), &mut inst);
                    inst.push(lir::Store::new(
                        lir::Variable::Local(values_loc),
                        lir::Variable::Local(item_loc).into(),
                        offset,
                        el_size,
                    ));

                    offset += el_size;
                }

                // allocate space for the list struct
                //   - values ptr: *'a
                //   - len: uint
                //   - capacity: uint
                let (list_loc, _) = ctx.new_loc(ty.clone());
                let list_ptr = lir::Malloc::new(lir::Size::ptrs(3));
                inst.push(lir::Inst::SetLocal(list_loc, list_ptr.into()));

                // store the values ptr
                inst.push(lir::Store::new(
                    lir::Variable::Local(list_loc),
                    lir::Variable::Local(values_loc).into(),
                    lir::Size::zero(),
                    lir::Size::ptr(),
                ));

                // store the length
                inst.push(lir::Store::new(
                    lir::Variable::Local(list_loc),
                    lir::Atom::UintConst(item_count as u64, lir::Size::ptr()).into(),
                    lir::Size::ptr(),
                    lir::Size::ptr(),
                ));

                // store the capacity
                inst.push(lir::Store::new(
                    lir::Variable::Local(list_loc),
                    lir::Atom::UintConst(capacity as u64, lir::Size::ptr()).into(),
                    lir::Size::ptrs(2),
                    lir::Size::ptr(),
                ));

                (inst, lir::Variable::Local(list_loc).into())
            }
            Expr::Asm(asm) => {
                let mut binops = asm
                    .inst
                    .iter()
                    .map(|(op, rands)| match op {
                        AsmOp::Malloc => lir::Malloc::new(match &rands[0] {
                            AsmOperand::Var(v) => {
                                if let Some(loc) = ctx.vars.get(v) {
                                    lir::Atom::new(lir::Variable::Local(*loc))
                                } else {
                                    let (idx, _) = ctx.new_var(v.clone(), ty.clone());
                                    lir::Atom::new(lir::Variable::Local(idx))
                                }
                            }
                            AsmOperand::Int(i) => lir::Size::bytes((*i) as usize).into(),
                        }),
                        _ => {
                            let mut binop = lir::BasicOp::from(*op);
                            binop.operands.extend(rands.iter().map(|rand| match rand {
                                AsmOperand::Var(v) => {
                                    if let Some(loc) = ctx.vars.get(v) {
                                        lir::Atom::new(lir::Variable::Local(*loc))
                                    } else {
                                        let (idx, _) = ctx.new_var(v.clone(), ty.clone());
                                        lir::Atom::new(lir::Variable::Local(idx))
                                    }
                                }
                                AsmOperand::Int(i) => lir::Atom::UintConst(*i, lir::Size::ptr()),
                            }));
                            lir::Value::BasicOp(binop)
                        }
                    })
                    .collect::<Vec<_>>();

                let mut inst = vec![];
                let value = if let Some(value) = binops.pop() {
                    let idx = ctx.get_or_set_local(value, ty.clone(), &mut inst);
                    lir::Value::new(lir::Variable::Local(idx))
                } else {
                    lir::Value::Empty
                };

                (inst, value)
            }
            Expr::Curly(curly) => {
                let ty = &curly.ty;
                let (loc, _) = ctx.new_loc(ty.clone());
                let mut size = lir::Size::zero();
                let mut field_insts = vec![];
                for field in curly.elements.iter() {
                    let (_, field_value) = variant!(&field.value, if CurlyElement::Labeled(x, y));
                    let field_ty = tcx.ty_of(field.id);
                    let field_size = field_ty.size_of();
                    let (inst, val) = field_value.lir_gen(ctx, tcx)?;
                    // note: since we're calculating the whole size, `size` is also the offset
                    field_insts.push((inst, val, field_ty, size, field_size));
                    size += field_size;
                }

                let mut inst = vec![];
                inst.push(lir::Inst::SetLocal(loc, lir::Malloc::new(size).into()));

                for (i, val, ty, offset, size) in field_insts {
                    inst.extend(i);
                    let field_loc = ctx.get_or_set_local(val, ty, &mut inst);
                    inst.push(lir::Store::new(
                        lir::Variable::Local(loc),
                        lir::Variable::Local(field_loc).into(),
                        offset,
                        size,
                    ));
                }

                (inst, lir::Variable::Local(loc).into())
            }
            Expr::Block(block) => {
                let (insts, mut vals): (Vec<_>, Vec<_>) =
                    block.stmts.lir_gen(ctx, tcx)?.into_iter().unzip();
                let val = vals.pop().unwrap_or_else(|| lir::Value::Empty);
                let mut inst = insts.concat();
                inst.extend(vals.into_iter().flat_map(|v| {
                    if !matches!(v, lir::Value::Empty) {
                        Some(v.into())
                    } else {
                        None
                    }
                }));
                (inst, val)
            }
            // HirNode::DerefAssign(lhs, rhs) => {
            //     let info = info.src_info().clone();
            //     let (mut inst, rhs_val) = rhs.lir_gen(ctx, tcx)?;
            //     let rhs_loc = ctx.get_or_set_local(rhs_val, info.clone(), rhs.ty(), &mut inst);
            //     let (lhs_inst, lhs_val) = lhs.lir_gen(ctx, tcx)?;
            //     inst.extend(lhs_inst);
            //     let size = rhs.ty().size_of();
            //     let lhs_loc = ctx.get_or_set_local(lhs_val, info.clone(), lhs.ty(), &mut inst);
            //     inst.push(Node::new(
            //         lir::Store::new(
            //             lir::Variable::Local(lhs_loc),
            //             lir::Variable::Local(rhs_loc).into(),
            //             lir::Size::zero(),
            //             size,
            //         ),
            //         info,
            //     ));
            //     (inst, lir::Value::Empty)
            // }
            Expr::Assign(assign) => {
                // generate the RHS
                let (mut inst, rhs_val) = assign.rhs.lir_gen(ctx, tcx)?;
                let rhs_ty = tcx.ty_of(assign.rhs.id);
                let rhs_loc = ctx.get_or_set_local(rhs_val, rhs_ty, &mut inst);

                // then the LHS
                let ty = tcx.ty_of(assign.lhs.id);
                let (lhs_inst, lhs_val) = (&assign.lhs.value, &ty).lir_gen(ctx, tcx)?;
                inst.extend(lhs_inst);
                let lhs_loc = ctx.get_or_set_local(lhs_val, ty.clone(), &mut inst);

                inst.push(lir::Inst::SetLocal(
                    lhs_loc,
                    lir::Atom::new(lir::Variable::Local(rhs_loc)).into(),
                ));
                (inst, lir::Value::Empty)
            }
            Expr::Fn(_) => todo!(),
            Expr::Dot(dot) => {
                let (mut inst, lhs_val) = dot.lhs.lir_gen(ctx, tcx)?;
                let lhs_ty = tcx.ty_of(dot.lhs.id);
                let lhs_loc = ctx.get_or_set_local(lhs_val, lhs_ty.clone(), &mut inst);

                (
                    inst,
                    lir::GetField {
                        src: lir::Variable::Local(lhs_loc),
                        field: dot.rhs.path.to_string(),
                    }
                    .into(),
                )
            }
            Expr::Call(call) => {
                let fn_ty = tcx.ty_of(call.lhs.id);
                let poly_ty = if let Ty::Var(original_ty) = tcx.original_ty_of(&call.lhs) {
                    ctx.inst_map.get(&original_ty).cloned().and_then(|t| {
                        if t.is_polymorphic() {
                            Some(t)
                        } else {
                            None
                        }
                    })
                } else {
                    None
                };

                let mut inst = vec![];
                let mut call_args: Vec<lir::Variable> = vec![];
                let base = if let Expr::Dot(dot) = &call.lhs.value {
                    let self_ty = tcx.ty_of(dot.lhs.id);
                    let (self_inst, self_val) = dot.lhs.lir_gen(ctx, tcx)?;
                    inst.extend(self_inst);

                    let self_path = self_ty.get_path().unwrap();
                    let self_loc = ctx.get_or_set_local(self_val, self_ty, &mut inst);
                    call_args.push(lir::Variable::Local(self_loc));

                    Some(self_path.append(dot.rhs.path.name().unwrap()))
                } else {
                    call.lhs.path()
                };

                let fn_name = base.map(|base| {
                    if !ctx.is_extern(&base) {
                        if let Some(poly_ty) = &poly_ty {
                            sema::fn_name(&base, poly_ty)
                        } else {
                            sema::fn_name(&base, &fn_ty)
                        }
                    } else {
                        base
                    }
                });

                for arg in call.args.items.iter() {
                    let arg_ty = tcx.ty_of(arg.id);
                    let (arg_inst, arg_val) = arg.lir_gen(ctx, tcx)?;
                    inst.extend(arg_inst);
                    let arg_loc = ctx.get_or_set_local(arg_val, arg_ty, &mut inst);
                    call_args.push(lir::Variable::Local(arg_loc));
                }

                let val = if let Some(fn_name) = fn_name {
                    log::debug!("add sym: {}", fn_name);
                    ctx.add_sym(fn_name.clone());
                    lir::Call::new(fn_name, call_args, fn_ty.clone(), poly_ty)
                } else {
                    let (mut inst, val) = call.lhs.lir_gen(ctx, tcx)?;
                    let fun_loc = ctx.get_or_set_local(val, fn_ty.clone(), &mut inst);
                    lir::Call::new_ref(fun_loc, call_args, fn_ty.clone(), poly_ty)
                };

                (inst, val)
            }
            Expr::BinOp(_) => todo!("lir_gen: Expr::BinOp: {}", ex),
            Expr::Break(_) => todo!("lir_gen: Expr::Break: {}", ex),
            Expr::Closure(_) => todo!("lir_gen: Expr::Closure: {}", ex),
            Expr::DefaultValue(_) => todo!("lir_gen: Expr::DefaultValue: {}", ex),
            Expr::For(_) => todo!("lir_gen: Expr::For: {}", ex),
            Expr::If(if_ex) => {
                log::debug!("type of: {}", ty);
                let (mut cond_inst, cond_val) = if_ex.cond.lir_gen(ctx, tcx)?;
                let cond_loc = ctx.get_or_set_local(cond_val, Ty::bool(), &mut cond_inst);

                let cond_label = ctx.new_label();
                let then_label = ctx.new_label();
                let else_label = ctx.new_label();

                let then_ty = tcx.ty_of(if_ex.then.id);
                log::debug!("then_ty = {}", then_ty);
                let (mut then_inst, then_val) = if_ex.then.lir_gen(ctx, tcx)?;
                let then_loc = ctx.get_or_set_local(then_val, then_ty.clone(), &mut then_inst);

                let (mut else_inst, else_loc, else_ty) = if let Some(else_ex) = if_ex.els.as_deref()
                {
                    let else_ty = tcx.ty_of(else_ex.id);
                    let (mut else_inst, else_val) = else_ex.lir_gen(ctx, tcx)?;
                    let else_loc = ctx.get_or_set_local(else_val, else_ty.clone(), &mut else_inst);
                    (else_inst, else_loc, else_ty)
                } else {
                    let (else_loc, _) = ctx.new_loc(Ty::nil());
                    let else_inst = vec![lir::Inst::SetLocal(
                        else_loc,
                        lir::Atom::UintConst(0, lir::Size::bytes(1)).into(),
                    )];
                    (else_inst, else_loc, Ty::nil())
                };

                cond_inst.push(
                    lir::Value::new(lir::Branch::new(
                        lir::BranchOp::BranchNZ,
                        lir::Variable::Local(cond_loc).into(),
                        then_label.clone(),
                        else_label.clone(),
                    ))
                    .into(),
                );

                let cond_block = lir::Block {
                    name: cond_label,
                    instructions: cond_inst,
                };

                let then_block = lir::Block {
                    name: then_label,
                    instructions: then_inst,
                };

                let else_block = lir::Block {
                    name: else_label,
                    instructions: else_inst,
                };

                let (if_loc, _) = ctx.new_loc(ty.clone());
                let phi = (
                    if_loc,
                    lir::Phi::new(
                        lir::Variable::Local(then_loc),
                        lir::Variable::Local(else_loc),
                    ),
                );
                let inst = vec![lir::IfBlock::new(cond_block, then_block, else_block, phi).into()];
                (inst, lir::Variable::Local(if_loc).into())
            }
            Expr::Index(_) => todo!("lir_gen: Expr::Index: {}", ex),
            Expr::Labeled(_, _) => todo!("lir_gen: Expr::Labeled: {}", ex),
            Expr::Loop(_) => todo!("lir_gen: Expr::Loop: {}", ex),
            Expr::Return(_) => todo!("lir_gen: Expr::Return: {}", ex),
            Expr::Sequence(_) => todo!("lir_gen: Expr::Sequence: {}", ex),
            Expr::Type(_) => todo!("lir_gen: Expr::Type: {}", ex),
            Expr::UnaryOp(_) => todo!("lir_gen: Expr::UnaryOp: {}", ex),
            Expr::Unsafe(_) => todo!("lir_gen: Expr::Unsafe: {}", ex),
            Expr::While(_) => todo!("lir_gen: Expr::While: {}", ex),
        })
    }
}

impl LirGen<GenResult> for (&Pattern, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        let &(pat, ty) = self;
        match pat {
            Pattern::Name(v) => {
                let var = v.to_string();
                Ok(if let Some(loc) = ctx.vars.get(&var) {
                    (vec![], lir::Value::new(lir::Variable::Local(*loc)))
                } else {
                    let (idx, _) = ctx.new_var(var, ty.clone());
                    (vec![], lir::Value::new(lir::Variable::Local(idx)))
                })
            }
            Pattern::Sequence(_) => todo!(),
            Pattern::Tuple(_) => todo!(),
        }
    }
}

impl LirGen<GenResult> for (&Path, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        let &(v, ty) = self;
        let var = v.to_string();
        Ok(if let Some(loc) = ctx.vars.get(&var) {
            (vec![], lir::Value::new(lir::Variable::Local(*loc)))
        } else {
            let (idx, _) = ctx.new_var(var, ty.clone());
            (vec![], lir::Value::new(lir::Variable::Local(idx)))
        })
    }
}

impl LirGen<GenResult> for (&Literal, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        let &(lit, ty) = self;
        let val = match lit {
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
            Literal::Float { value, size } => todo!(),
            Literal::String(s) => {
                let mut inst = vec![];
                // convert the string to bytes and add a `Data` to the program
                let bytes = s.as_bytes().to_vec();
                let len = bytes.len();
                let idx = ctx.data(bytes);

                // store the size in a variable so we can re-use it
                let (size_loc, _) = ctx.new_loc(Ty::uint());
                let size = lir::Size::bytes(len);
                inst.push(lir::Inst::SetLocal(size_loc, lir::Atom::Size(size).into()));

                // allocate a pointer to store the string bytes
                let (data_loc, _) = ctx.new_loc(Ty::ptr(Ty::u8()));
                let ptr = lir::Malloc::new(lir::Variable::Local(size_loc));
                inst.push(lir::Inst::SetLocal(data_loc, ptr.into()));

                // make a call to `memcpy` to copy the bytes
                inst.push(lir::Inst::MemCopy(
                    lir::Variable::Local(data_loc), // dst
                    lir::Variable::Data(idx),       // src
                    lir::Variable::Local(size_loc), // size
                ));

                // create a `string` struct
                //  - raw_ptr: *u8
                //  - size: usize
                let (loc, _) = ctx.new_loc(Ty::string());
                let size = lir::Size::ptrs(2);
                let ptr = lir::Malloc::new(size);
                inst.push(lir::Inst::SetLocal(loc, ptr.into()));

                // store the pointer to the bytes
                inst.push(lir::Store::new(
                    lir::Variable::Local(loc),
                    lir::Variable::Local(data_loc).into(),
                    lir::Size::zero(),
                    lir::Size::ptr(),
                ));

                // store the size of the string
                inst.push(lir::Store::new(
                    lir::Variable::Local(loc),
                    lir::Variable::Local(size_loc).into(),
                    lir::Size::ptr(),
                    lir::Size::ptr(),
                ));

                return Ok((inst, lir::Atom::new(lir::Variable::Local(loc)).into()));
            }
            Literal::ByteString(_) => todo!(),
            Literal::Byte(_) => todo!(),
            Literal::Char(ch) => lir::Atom::UintConst(*ch as u64, lir::Size::bytes(4)).into(),
            Literal::Bool(b) => {
                lir::Atom::UintConst(if *b { 1 } else { 0 }, lir::Size::bytes(1)).into()
            }
            Literal::UnicodeEscSeq(_) => todo!(),
            Literal::Unit => lir::Value::Empty,
            Literal::Nil => lir::Atom::UintConst(0, lir::Size::bytes(1)).into(),
        };

        Ok((vec![], val))
    }
}

// impl LirGen<GenResult> for HirNode {
//     fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
//         if let HirNode::Typed(t) = &self {
//             let ty = t.ty();
//             (&t.value, &t.info, &ty).lir_gen(ctx, tcx)
//         } else {
//             unreachable!("unexpected untyped HirNode: {}", self)
//         }
//     }
// }

impl LirGen<GenResult> for (&Decl, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        let &(decl, ty) = self;
        match decl {
            Decl::Fn(func) => return (func, ty).lir_gen(ctx, tcx),
            Decl::Mutable(_) | Decl::Name(_) => {
                todo!()
            }
            Decl::Trait(tr) => {
                for func in tr.funcs.iter() {
                    ctx.add_trait_member(func.path.clone());
                }
            }
            Decl::Impl(imp) => {
                if let Some(funcs) = &imp.funcs {
                    for func in funcs {
                        let ty = tcx.ty_of(func.id);
                        let func = variant!(&func.value, if Decl::Fn(f));
                        (func, &ty).lir_gen(ctx, tcx)?;
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
                        ctx.new_extern(name.path.clone(), ty, is_mutable, src.clone());
                    }
                    Decl::FnSig(sig) => {
                        ctx.new_extern(sig.path.clone(), ty.clone(), false, src.clone());
                    }
                    d @ _ => unreachable!("lir_gen Decl::Extern: {:?}", d),
                }
            }
            Decl::Declare(_) => todo!(),
            Decl::FnSig(_) => todo!(),
            Decl::TypeAlias(_, _) | Decl::Struct(_) => {}
        }

        Ok((vec![], lir::Value::Empty))
    }
}

impl LirGen<GenResult> for (&ast::Fn, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        let &(func, fn_ty) = self;

        let base = &func.sig.path;
        log::debug!("base function path: {}", base);
        log::debug!("function type: {}", fn_ty);
        let name = if !fn_ty.is_polymorphic() {
            sema::fn_name(base, &fn_ty)
        } else {
            base.clone()
        };

        log::debug!("full name: {}", name);
        let mut ctx = ctx.clone();
        ctx.fx = ctx.new_func(base.clone(), fn_ty.clone());
        ctx.label_idx = 0;

        // add the parameters to the function
        let mut inst = vec![];
        for p in func.sig.params.iter() {
            let name = p.name().unwrap().to_string();
            let ty = tcx.ty_of(p.id);
            ctx.new_param(name, ty);
        }

        let body = func.body.as_ref().unwrap();
        let (body_inst, body_val) = body.lir_gen(&mut ctx, tcx)?;
        inst.extend(body_inst);

        let (_, _, _, ret_ty) = fn_ty.try_borrow_fn().unwrap();
        if !ret_ty.is_unit() {
            let body_loc = ctx.get_or_set_local(body_val, tcx.ty_of(body.id), &mut inst);
            inst.push(lir::Inst::Return(lir::Variable::Local(body_loc).into()).into());
        } else {
            if !matches!(body_val, lir::Value::Empty) {
                inst.push(lir::Inst::Value(body_val));
            }
            inst.push(lir::Inst::Return(lir::Value::Empty).into());
        }

        let decs = func.sig.decorators.clone();
        let mut func = ctx.borrow_func_mut();
        func.name = name;
        func.body.instructions = inst;
        func.decorators = decs;

        Ok((vec![], lir::Value::Empty))
    }
}

// impl LirGen<GenResult> for (&Extern, &HirInfo) {
//     fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
//         let &(ext, info) = self;
//         todo!();
//     }
// }

impl LirGen<GenResult> for Node<Expr> {
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        // let scope = tcx.get(self).path;
        // let prev_scope = std::mem::replace(&mut ctx.scope, scope);
        let ty = tcx.ty_of(self.id);
        let res = (&self.value, &ty).lir_gen(ctx, tcx);
        // ctx.scope = prev_scope;
        res
    }
}

impl LirGen<GenResult> for Node<Decl> {
    fn lir_gen(&self, ctx: &mut GenCtx, tcx: &TyCtx) -> RayResult<GenResult> {
        // let scope = tcx.get(self).path;
        // let prev_scope = std::mem::replace(&mut ctx.scope, scope);
        let ty = tcx.ty_of(self.id);
        let res = (&self.value, &ty).lir_gen(ctx, tcx);
        // ctx.scope = prev_scope;
        res
    }
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

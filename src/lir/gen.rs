use std::{
    cell::{RefCell, RefMut},
    collections::HashMap,
    rc::Rc,
};

use lir::Store;

use crate::{
    ast::{self, asm::AsmOp, token::IntegerBase, Literal, Node, Path, SourceInfo},
    errors::RayResult,
    hir::{HirDecl, HirInfo, HirNode, HirPattern},
    lir, sema, sym,
    typing::{self, solvers::Solution, traits::HasType, ty::Ty, Subst},
};

impl lir::Program {
    pub fn gen(
        path: ast::Path,
        solution: &Solution,
        root: &Node<HirNode<HirInfo>, HirInfo>,
        tcx: typing::Ctx,
    ) -> RayResult<lir::Program> {
        let scope = path.clone();
        let mut prog = lir::Program::new(path);
        prog.start_idx = 0;
        prog.funcs.push(lir::Func::new(
            "_start",
            scope.append("_start"),
            Ty::Func(vec![], Box::new(Ty::unit())),
        ));
        let prog = Rc::new(RefCell::new(prog));
        let mut ctx = GenCtx::new(Rc::clone(&prog), solution.inst_map.clone(), tcx);
        let (mut inst, _) = root.lir_gen(&mut ctx)?;

        inst.push(Node::new(
            lir::Inst::Return(lir::Value::Empty).into(),
            SourceInfo::empty(),
        ));
        drop(ctx);

        // take the prog out of the pointer
        let mut prog = Rc::try_unwrap(prog).unwrap().into_inner();
        prog.funcs
            .get_mut(0)
            .unwrap()
            .body
            .instructions
            .extend(inst);

        Ok(prog)
    }

    pub fn monomorphize(&mut self) {
        let mut mr = sema::Monomorphizer::new(self);
        let entry = self.funcs.get_mut(self.start_idx as usize).unwrap();
        let funcs = mr.monomorphize(entry);

        // remove the polymorphic functions
        let mut i = 0;
        while i < self.funcs.len() {
            let f = &self.funcs[i];
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
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<T>;
}

#[derive(Clone, Debug)]
pub struct GenCtx {
    prog: Rc<RefCell<lir::Program>>,
    scope: Path,
    fx: usize,
    fn_idx: HashMap<String, usize>,
    data_idx: HashMap<Vec<u8>, usize>,
    module_cache: HashMap<String, sym::Symbol>,
    vars: HashMap<String, usize>,
    inst_map: Subst,
    tcx: typing::Ctx,
}

impl GenCtx {
    fn new(prog: Rc<RefCell<lir::Program>>, inst_map: Subst, tcx: typing::Ctx) -> GenCtx {
        let scope = prog.borrow().module_path.clone();
        GenCtx {
            prog,
            scope,
            fx: 0,
            fn_idx: HashMap::new(),
            data_idx: HashMap::new(),
            module_cache: HashMap::new(),
            vars: HashMap::new(),
            inst_map,
            tcx,
        }
    }

    fn new_loc_with(
        locals: &mut Vec<lir::Local>,
        ty: Ty,
        name: Option<String>,
    ) -> (usize, lir::Size) {
        let idx = locals.len();
        let size = GenCtx::size_of(&ty);
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

    fn add_sym(&mut self, sym: String) {
        self.borrow_func_mut().symbols.insert(sym);
    }

    fn new_func(&mut self, name: String, ty: Ty) -> usize {
        let mut prog = self.prog.borrow_mut();
        let idx = prog.funcs.len();
        if ty.is_polymorphic() {
            prog.poly_fn_map.insert(name.clone(), idx);
        }

        let scope = self.scope.append(&name);
        prog.funcs.push(lir::Func::new(name, scope, ty));
        idx
    }

    fn is_poly_func(&self, name: &String) -> bool {
        let prog = self.prog.borrow();
        prog.poly_fn_map.contains_key(name)
    }

    fn borrow_func_mut(&mut self) -> RefMut<'_, lir::Func> {
        let prog = self.prog.borrow_mut();
        RefMut::map(prog, |p| p.funcs.get_mut(self.fx).unwrap())
    }

    fn new_extern(&mut self, name: String, ty: Ty, is_mutable: bool, src: Option<String>) {
        let mut prog = self.prog.borrow_mut();
        prog.extern_set.insert(name.clone());
        prog.externs.push(lir::Extern {
            name,
            ty,
            is_mutable,
            src,
        });
    }

    fn add_trait_member(&mut self, name: String) {
        let mut prog = self.prog.borrow_mut();
        prog.trait_member_set.insert(name.clone());
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

    fn get_or_set_local(
        &mut self,
        value: lir::Value,
        info: SourceInfo,
        ty: Ty,
        inst: &mut Vec<Node<lir::Inst, SourceInfo>>,
    ) -> usize {
        if let lir::Value::Atom(lir::Atom::Variable(lir::Variable::Local(idx))) = value {
            idx
        } else {
            let (idx, _) = self.new_loc(ty.clone());
            inst.push(Node::new(
                lir::Inst::SetLocal(idx, value.clone()).into(),
                info,
            ));
            idx
        }
    }

    fn size_of(ty: &Ty) -> lir::Size {
        match ty {
            Ty::Never | Ty::Any | Ty::Var(_) => lir::Size::zero(),
            Ty::Tuple(t) => t.iter().map(GenCtx::size_of).sum(),
            Ty::Union(v) => {
                let tag_size = (v.len() + 7) / 8;
                let max_size = v.iter().map(GenCtx::size_of).max().unwrap_or_default();
                lir::Size::bytes(tag_size) + max_size
            }
            Ty::Func(_, _) | Ty::Ptr(_) => lir::Size::ptr(),
            Ty::Projection(n, _, _) => match n.as_str() {
                "int" | "uint" => lir::Size::ptr(),
                "i8" | "u8" => lir::Size::bytes(1),
                "i16" | "u16" => lir::Size::bytes(2),
                "i32" | "u32" | "f32" => lir::Size::bytes(4),
                "i64" | "u64" | "f64" => lir::Size::bytes(8),
                "i128" | "u128" | "f128" => lir::Size::bytes(16),
                // _ if f.len() != 0 => f
                //     .iter()
                //     .fold(lir::Size::zero(), |acc, ty| acc + GenCtx::size_of(ty)),
                _ => lir::Size::ptr(),
            },
            Ty::Cast(_, ty) | Ty::Qualified(_, ty) | Ty::All(_, ty) => GenCtx::size_of(ty),
        }
    }
}

pub type GenResult = (Vec<Node<lir::Inst, SourceInfo>>, lir::Value);

impl LirGen<GenResult> for (&HirNode<HirInfo>, &HirInfo, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<GenResult> {
        let &(hir, info, ty) = self;
        Ok(match hir {
            HirNode::Var(v) => (v, ty).lir_gen(ctx)?,
            HirNode::Literal(lit) => return (lit, info, ty).lir_gen(ctx),
            HirNode::Type(t) => todo!(),
            HirNode::Tuple(els) => {
                let mut inst = vec![];
                let tys = variant!(ty, if Ty::Tuple(tys));

                // create a new local for the tuple and then make an allocation
                let (tuple_loc, size) = ctx.new_loc(ty.clone());
                let value = if !size.is_zero() {
                    let ptr = lir::Malloc::new(size);
                    inst.push(Node::new(
                        lir::Inst::SetLocal(tuple_loc, ptr.into()),
                        info.src_info().clone(),
                    ));

                    // for each element of the tuple, store it on the stack
                    let mut offset = lir::Size::zero();
                    for (el, ty) in els.iter().zip(tys.iter().cloned()) {
                        // generate the lir for the element
                        let (el_inst, val) = el.lir_gen(ctx)?;
                        let size = GenCtx::size_of(&ty);
                        inst.extend(el_inst);
                        let el_loc =
                            ctx.get_or_set_local(val, info.src_info().clone(), ty, &mut inst);

                        // store the element on the stack
                        inst.push(Node::new(
                            lir::Store::new(
                                lir::Variable::Local(tuple_loc),
                                lir::Atom::new(lir::Variable::Local(el_loc)).into(),
                                offset,
                                size,
                            ),
                            el.info.src_info().clone(),
                        ));

                        offset += size;
                    }

                    lir::Value::new(lir::Variable::Local(tuple_loc))
                } else {
                    lir::Value::new(lir::Atom::NilConst)
                };

                (inst, value)
            }
            HirNode::Asm(ty, insts) => {
                let mut binops = insts
                    .iter()
                    .map(|(op, rands)| match op {
                        AsmOp::Malloc => {
                            let v = &rands[0];
                            lir::Malloc::new(if let Some(loc) = ctx.vars.get(v) {
                                lir::Atom::new(lir::Variable::Local(*loc))
                            } else {
                                let (idx, _) = ctx.new_var(v.clone(), ty.clone().unwrap());
                                lir::Atom::new(lir::Variable::Local(idx))
                            })
                        }
                        _ => {
                            let mut binop = lir::BasicOp::from(*op);
                            binop.operands.extend(rands.iter().map(|v| {
                                if let Some(loc) = ctx.vars.get(v) {
                                    lir::Atom::new(lir::Variable::Local(*loc))
                                } else {
                                    let (idx, _) = ctx.new_var(v.clone(), ty.clone().unwrap());
                                    lir::Atom::new(lir::Variable::Local(idx))
                                }
                            }));
                            lir::Value::BasicOp(binop)
                        }
                    })
                    .collect::<Vec<_>>();

                let mut inst = vec![];
                let value = if let Some(value) = binops.pop() {
                    let idx = ctx.get_or_set_local(
                        value,
                        info.src_info().clone(),
                        ty.clone().unwrap(),
                        &mut inst,
                    );
                    lir::Value::new(lir::Variable::Local(idx))
                } else {
                    lir::Value::Empty
                };

                (inst, value)
            }
            HirNode::Cast(ex, ty) => todo!(),
            HirNode::Decl(dec) => todo!(),
            HirNode::Struct(fqn, ty, fields) => {
                let src_info = info.src_info().clone();
                let (loc, _) = ctx.new_loc(ty.clone());
                let mut size = lir::Size::zero();
                let mut field_insts = vec![];
                for (name, field) in fields {
                    let field_ty = field.ty();
                    let field_size = GenCtx::size_of(&field_ty);
                    let (inst, val) = field.lir_gen(ctx)?;
                    // note: since we're calculating the whole size, `size` is also the offset
                    field_insts.push((
                        inst,
                        val,
                        field.info.src_info().clone(),
                        field_ty,
                        size,
                        field_size,
                    ));
                    size += field_size;
                }

                let mut inst = vec![];
                inst.push(Node::new(
                    lir::Inst::SetLocal(loc, lir::Malloc::new(size).into()),
                    src_info.clone(),
                ));

                for (i, val, info, ty, offset, size) in field_insts {
                    inst.extend(i);
                    let field_loc = ctx.get_or_set_local(val, info.clone(), ty, &mut inst);
                    inst.push(Node::new(
                        lir::Store::new(
                            lir::Variable::Local(loc),
                            lir::Variable::Local(field_loc).into(),
                            offset,
                            size,
                        ),
                        info,
                    ));
                }

                (inst, lir::Variable::Local(loc).into())
            }
            HirNode::Block(stmts) => {
                let (insts, mut vals): (Vec<_>, Vec<_>) = stmts.lir_gen(ctx)?.into_iter().unzip();
                let inst = insts.concat();
                (inst, vals.pop().unwrap_or_else(|| lir::Value::Empty))
            }
            HirNode::Let(decls, body) => {
                let mut inst = decls
                    .lir_gen(ctx)?
                    .into_iter()
                    .flat_map(|(i, _)| i)
                    .collect::<Vec<_>>();
                let (body_inst, val) = body.lir_gen(ctx)?;
                inst.extend(body_inst);
                (inst, val)
            }
            HirNode::Fun(params, body, decs) => todo!(),
            HirNode::Dot(lhs, n) => {
                let (mut inst, lhs_val) = lhs.lir_gen(ctx)?;
                let lhs_loc =
                    ctx.get_or_set_local(lhs_val, info.src_info().clone(), lhs.ty(), &mut inst);

                // get the field offset and size
                let lhs_fqn = lhs.ty().get_path().unwrap();
                let lhs_ty = ctx.tcx.get_struct_ty(&lhs_fqn).unwrap();
                let mut offset = lir::Size::zero();
                let mut size = lir::Size::zero();
                for (name, field_ty) in lhs_ty.fields.iter() {
                    size = GenCtx::size_of(field_ty);
                    if name == n.name() {
                        break;
                    }
                    offset += size;
                }

                (
                    inst,
                    lir::Load {
                        src: lir::Variable::Local(lhs_loc),
                        offset,
                        size,
                    }
                    .into(),
                )
            }
            HirNode::Apply(fun, args) => {
                let poly_ty = if let Ty::Var(original_ty) = fun.info.original_ty() {
                    ctx.inst_map.get(original_ty).cloned().and_then(|t| {
                        if t.is_polymorphic() {
                            Some(t)
                        } else {
                            None
                        }
                    })
                } else {
                    None
                };
                let fn_ty = fun.ty();
                let mut inst = vec![];
                let mut call_args: Vec<lir::Variable> = vec![];
                for arg in args.iter() {
                    let arg_ty = arg.ty();
                    let (arg_inst, arg_val) = arg.lir_gen(ctx)?;
                    inst.extend(arg_inst);
                    let arg_loc =
                        ctx.get_or_set_local(arg_val, info.src_info().clone(), arg_ty, &mut inst);
                    call_args.push(lir::Variable::Local(arg_loc));
                }

                let val = if let Some(fn_name) = fun.fn_name() {
                    ctx.add_sym(fn_name.clone());
                    lir::Call::new(fn_name.clone(), call_args, fn_ty.clone(), poly_ty)
                } else {
                    let (mut inst, val) = fun.lir_gen(ctx)?;
                    let fun_loc = ctx.get_or_set_local(
                        val,
                        info.src_info().clone(),
                        fn_ty.clone(),
                        &mut inst,
                    );
                    lir::Call::new_ref(fun_loc, call_args, fn_ty.clone(), poly_ty)
                };

                let (_, _, _, ret_ty) = fn_ty.try_borrow_fn().unwrap();
                let idx =
                    ctx.get_or_set_local(val, info.src_info().clone(), ret_ty.clone(), &mut inst);
                (inst, lir::Variable::Local(idx).into())
            }
            HirNode::Typed(t) => return t.lir_gen(ctx),
        })
    }
}

impl LirGen<GenResult> for (&String, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<GenResult> {
        let &(v, ty) = self;
        Ok(if let Some(loc) = ctx.vars.get(v) {
            (vec![], lir::Value::new(lir::Variable::Local(*loc)))
        } else {
            let (idx, _) = ctx.new_var(v.clone(), ty.clone());
            (vec![], lir::Value::new(lir::Variable::Local(idx)))
        })
    }
}

impl LirGen<GenResult> for (&Literal, &HirInfo, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<GenResult> {
        let &(lit, info, ty) = self;
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
                let info = info.src_info().clone();
                let mut inst = vec![];
                // convert the string to bytes and add a `Data` to the program
                let bytes = s.as_bytes().to_vec();
                let len = bytes.len();
                let idx = ctx.data(bytes);

                // store the size in a variable so we can re-use it
                let (size_loc, _) = ctx.new_loc(Ty::uint());
                let size = lir::Size::bytes(len);
                inst.push(Node::new(
                    lir::Inst::SetLocal(size_loc, lir::Atom::Size(size).into()),
                    info.clone(),
                ));

                // allocate a pointer to store the string bytes
                let (data_loc, _) = ctx.new_loc(Ty::ptr(Ty::u8()));
                let ptr = lir::Malloc::new(lir::Variable::Local(size_loc));
                inst.push(Node::new(
                    lir::Inst::SetLocal(data_loc, ptr.into()),
                    info.clone(),
                ));

                // make a call to `memcpy` to copy the bytes
                inst.push(Node::new(
                    lir::Inst::MemCopy(
                        lir::Variable::Local(data_loc), // dst
                        lir::Variable::Data(idx),       // src
                        lir::Variable::Local(size_loc), // size
                    ),
                    info.clone(),
                ));

                // create a `string` struct
                //  - size: usize
                //  - raw_ptr: *u8
                let (loc, _) = ctx.new_loc(Ty::string());
                let size = lir::Size::ptrs(2);
                let ptr = lir::Malloc::new(size);
                inst.push(Node::new(
                    lir::Inst::SetLocal(loc, ptr.into()),
                    info.clone(),
                ));

                // store the size of the string
                inst.push(Node::new(
                    lir::Store::new(
                        lir::Variable::Local(loc),
                        lir::Variable::Local(size_loc).into(),
                        lir::Size::zero(),
                        lir::Size::ptr(),
                    ),
                    info.clone(),
                ));

                // store the pointer to the bytes
                inst.push(Node::new(
                    lir::Store::new(
                        lir::Variable::Local(loc),
                        lir::Variable::Local(data_loc).into(),
                        lir::Size::ptr(),
                        lir::Size::ptr(),
                    ),
                    info,
                ));

                return Ok((inst, lir::Atom::new(lir::Variable::Local(loc)).into()));
            }
            Literal::ByteString(_) => todo!(),
            Literal::Byte(_) => todo!(),
            Literal::Char(_) => todo!(),
            Literal::Bool(_) => todo!(),
            Literal::UnicodeEscSeq(_) => todo!(),
            Literal::Unit => lir::Value::Empty,
            Literal::Nil => todo!(),
        };

        Ok((vec![], val))
    }
}

impl LirGen<GenResult> for HirNode<HirInfo> {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<GenResult> {
        if let HirNode::Typed(t) = &self {
            let ty = t.ty();
            (&t.value, &t.info, &ty).lir_gen(ctx)
        } else {
            unreachable!("unexpected untyped HirNode: {}", self)
        }
    }
}

impl LirGen<GenResult> for (&HirDecl<HirInfo>, &HirInfo) {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<GenResult> {
        let &(decl, info) = self;
        Ok(match decl {
            HirDecl::Pattern(p, d) => match p {
                HirPattern::Var(name) => {
                    let ty = d.ty();
                    let mut ex = &d.value;
                    if let HirNode::Typed(t) = ex {
                        ex = &t.value;
                    }

                    if let HirNode::Fun(params, body, decs) = ex {
                        let mut ctx = ctx.clone();
                        ctx.fx = ctx.new_func(name.clone(), ty.clone());

                        // add the parameters to the function
                        let mut inst = vec![];
                        for p in params {
                            let name = p.get_name().clone();
                            let ty = p.get_ty().unwrap().clone();
                            ctx.new_param(name, ty);
                        }

                        let (body_inst, body_val) = body.lir_gen(&mut ctx)?;
                        inst.extend(body_inst);

                        let (_, _, _, ret_ty) = ty.try_borrow_fn().unwrap();
                        let body_info = body.info.src_info();
                        if !ret_ty.is_unit() {
                            let body_loc = ctx.get_or_set_local(
                                body_val,
                                body_info.clone(),
                                body.ty(),
                                &mut inst,
                            );
                            inst.push(Node::new(
                                lir::Inst::Return(lir::Variable::Local(body_loc).into()).into(),
                                body_info.clone(),
                            ));
                        } else {
                            inst.push(Node::new(
                                lir::Inst::Return(lir::Value::Empty).into(),
                                body_info.clone(),
                            ));
                        }

                        let mut func = ctx.borrow_func_mut();
                        func.body.instructions = inst;
                        func.decorators = decs.clone();
                        return Ok((vec![], lir::Value::Empty));
                    }

                    // generate the RHS
                    let (mut inst, rhs_val) = d.lir_gen(ctx)?;
                    let src_info = d.info.src_info();
                    let rhs_loc =
                        ctx.get_or_set_local(rhs_val, src_info.clone(), d.ty(), &mut inst);

                    // then the LHS
                    let (lhs_inst, lhs_val) = (name, &ty).lir_gen(ctx)?;
                    inst.extend(lhs_inst);
                    let lhs_loc = ctx.get_or_set_local(
                        lhs_val,
                        info.src_info().clone(),
                        ty.clone(),
                        &mut inst,
                    );

                    inst.push(Node::new(
                        lir::Inst::SetLocal(
                            lhs_loc,
                            lir::Atom::new(lir::Variable::Local(rhs_loc)).into(),
                        ),
                        info.src_info().clone(),
                    ));
                    (inst, lir::Value::Empty)
                }
            },
            HirDecl::Type(name, ty, is_mutable, src) => {
                ctx.new_extern(name.clone(), ty.clone(), *is_mutable, src.clone());
                (vec![], lir::Value::Empty)
            }
            HirDecl::TraitMember(name, _) => {
                ctx.add_trait_member(name.clone());
                (vec![], lir::Value::Empty)
            }
        })
    }
}

impl LirGen<GenResult> for Node<HirNode<HirInfo>, HirInfo> {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<GenResult> {
        let scope = self.info.path().clone();
        let prev_scope = std::mem::replace(&mut ctx.scope, scope);
        let ty = self.ty();
        let res = (&self.value, &self.info, &ty).lir_gen(ctx);
        ctx.scope = prev_scope;
        res
    }
}

impl LirGen<GenResult> for Node<HirDecl<HirInfo>, HirInfo> {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<GenResult> {
        let scope = self.info.path().clone();
        let prev_scope = std::mem::replace(&mut ctx.scope, scope);
        let res = (&self.value, &self.info).lir_gen(ctx);
        ctx.scope = prev_scope;
        res
    }
}

impl<T> LirGen<Vec<GenResult>> for Vec<T>
where
    T: LirGen<GenResult>,
{
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<Vec<GenResult>> {
        self.iter()
            .map(|t| t.lir_gen(ctx))
            .collect::<RayResult<Vec<_>>>()
    }
}

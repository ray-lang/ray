use std::{
    cell::{RefCell, RefMut},
    collections::HashMap,
    rc::Rc,
};

use crate::{
    ast::{self, token::IntegerBase, Literal, Node, Path, SourceInfo},
    errors::RayResult,
    hir::{HirDecl, HirInfo, HirNode, HirPattern},
    lir, sema, sym,
    typing::{solvers::Solution, traits::HasType, ty::Ty, Subst},
};

impl lir::Program {
    pub fn gen(
        path: ast::Path,
        solution: &Solution,
        root: &Node<HirNode<HirInfo>, HirInfo>,
    ) -> RayResult<lir::Program> {
        let scope = path.clone();
        let mut prog = lir::Program::new(path);
        prog.main = 0;
        prog.funcs.push(lir::Func::new(
            "main",
            scope.append("main"),
            Ty::Func(vec![], Box::new(Ty::unit())),
        ));
        let prog = Rc::new(RefCell::new(prog));
        let mut ctx = GenCtx::new(Rc::clone(&prog), solution.inst_map.clone());
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
        let entry = self.funcs.get_mut(self.main as usize).unwrap();
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
    module_cache: HashMap<String, sym::Symbol>,
    vars: HashMap<String, usize>,
    inst_map: Subst,
}

impl GenCtx {
    fn new(prog: Rc<RefCell<lir::Program>>, inst_map: Subst) -> GenCtx {
        let scope = prog.borrow().module_path.clone();
        GenCtx {
            prog,
            scope,
            fx: 0,
            fn_idx: HashMap::new(),
            module_cache: HashMap::new(),
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

    fn new_extern(&mut self, name: String, ty: Ty) {
        let mut prog = self.prog.borrow_mut();
        prog.extern_set.insert(name.clone());
        prog.externs.push(lir::Extern {
            name,
            ty,
            is_c: true,
        });
    }

    // fn new_poly_fn_ref(&mut self, name: String, callee_ty: Ty) -> String {
    //     let mut prog = self.prog.borrow_mut();
    //     let f = prog.poly_fn_map.get(&name).unwrap();
    //     let fun = prog.funcs.get(*f).unwrap();
    //     let poly_ty = fun.ty.clone();
    //     let tmp_name = rand_string(32);
    //     prog.poly_fn_refs.push(lir::PolyFnRef {
    //         name,
    //         tmp_name: tmp_name.clone(),
    //         // fn_ctx: self.fx,
    //         poly_ty,
    //         callee_ty: lir::FnType::from(callee_ty),
    //     });
    //     tmp_name
    // }

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
            Ty::Union(v) => {
                let tag_size = ((v.len() + 7) / 8) as u64;
                let max_size = v
                    .iter()
                    .map(|ty| GenCtx::size_of(ty))
                    .max()
                    .unwrap_or_default();
                lir::Size::bytes(tag_size) + max_size
            }
            Ty::Func(_, _) => lir::Size::ptr(),
            Ty::Projection(n, _, f) => match n.as_str() {
                "int" | "uint" => lir::Size::ptr(),
                "i8" | "u8" => lir::Size::bytes(1),
                "i16" | "u16" => lir::Size::bytes(2),
                "i32" | "u32" | "f32" => lir::Size::bytes(4),
                "i64" | "u64" | "f64" => lir::Size::bytes(8),
                "i128" | "u128" | "f128" => lir::Size::bytes(16),
                _ => f
                    .iter()
                    .fold(lir::Size::zero(), |acc, ty| acc + GenCtx::size_of(ty)),
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
            HirNode::Var(v) => {
                if let Some(loc) = ctx.vars.get(v) {
                    (vec![], lir::Value::new(lir::Variable::Local(*loc)))
                } else {
                    let (idx, _) = ctx.new_var(v.clone(), ty.clone());
                    (vec![], lir::Value::new(lir::Variable::Local(idx)))
                }
            }
            HirNode::Literal(lit) => return (lit, ty).lir_gen(ctx),
            HirNode::Type(t) => todo!(),
            HirNode::Cast(ex, ty) => todo!(),
            HirNode::Decl(dec) => todo!(),
            HirNode::Struct(name, fields) => todo!(),
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
            HirNode::Fun(params, body) => todo!(),
            HirNode::Apply(fun, args) => {
                let poly_ty = if let Ty::Var(original_ty) = fun.info.original_ty() {
                    log::debug!("original ty: {}", original_ty);
                    ctx.inst_map.get(original_ty).cloned()
                } else {
                    None
                };
                let fn_ty = fun.ty();
                log::debug!("apply fun type: {}", fn_ty);
                let mut inst = vec![];
                let mut arg_vals: Vec<lir::Atom> = vec![];
                for arg in args.iter() {
                    let arg_ty = arg.ty();
                    let (arg_inst, arg_val) = arg.lir_gen(ctx)?;
                    inst.extend(arg_inst);
                    let arg_loc =
                        ctx.get_or_set_local(arg_val, info.src_info().clone(), arg_ty, &mut inst);
                    arg_vals.push(lir::Variable::Local(arg_loc).into());
                }

                let val = if let Some(fn_name) = fun.fn_name() {
                    lir::Call::new(fn_name.clone(), arg_vals, fn_ty.clone(), poly_ty)
                } else {
                    let (mut inst, val) = fun.lir_gen(ctx)?;
                    let fun_loc = ctx.get_or_set_local(
                        val,
                        info.src_info().clone(),
                        fn_ty.clone(),
                        &mut inst,
                    );
                    lir::Call::new_ref(fun_loc, arg_vals, fn_ty.clone(), poly_ty)
                };

                let idx = ctx.get_or_set_local(val, info.src_info().clone(), fn_ty, &mut inst);
                (inst, lir::Variable::Local(idx).into())
            }
            HirNode::Typed(t) => return t.lir_gen(ctx),
        })
    }
}

impl LirGen<GenResult> for (&Literal, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<GenResult> {
        let &(lit, ty) = self;
        Ok((
            vec![],
            match lit {
                Literal::Integer {
                    value,
                    base,
                    size,
                    signed,
                } => match base {
                    IntegerBase::Decimal => {
                        let size = lir::Size::bytes((size / 8) as u64);
                        lir::Value::new(if !signed {
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
                Literal::String(_) => todo!(),
                Literal::ByteString(_) => todo!(),
                Literal::Byte(_) => todo!(),
                Literal::Char(_) => todo!(),
                Literal::Bool(_) => todo!(),
                Literal::UnicodeEscSeq(_) => todo!(),
                Literal::Unit => todo!(),
                Literal::Nil => todo!(),
            },
        ))
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

impl LirGen<GenResult> for HirDecl<HirInfo> {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<GenResult> {
        Ok(match &self {
            HirDecl::Pattern(p, d) => match p {
                HirPattern::Var(name) => {
                    let ty = d.ty();
                    let mut ex = &d.value;
                    if let HirNode::Typed(t) = ex {
                        ex = &t.value;
                    }

                    if let HirNode::Fun(params, body) = ex {
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
                        return Ok((vec![], lir::Value::Empty));
                    }

                    let (mut inst, val) = d.lir_gen(ctx)?;
                    let ty = d.ty();
                    let src_info = d.info.src_info();
                    let src = ctx.get_or_set_local(val, src_info.clone(), ty.clone(), &mut inst);
                    let (dst, size) = ctx.new_var(name.clone(), ty);
                    inst.push(Node::new(
                        lir::Inst::SetLocal(
                            dst,
                            lir::Load {
                                src: lir::Variable::Local(src),
                                offset: lir::Size::zero(),
                                size,
                            }
                            .into(),
                        )
                        .into(),
                        src_info.clone(),
                    ));
                    (inst, lir::Value::new(lir::Variable::Local(dst)))
                }
            },
            HirDecl::Type(name, ty) => {
                ctx.new_extern(name.clone(), ty.clone());
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
        let res = self.value.lir_gen(ctx);
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

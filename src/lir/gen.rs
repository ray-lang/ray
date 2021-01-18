use std::{
    cell::{RefCell, RefMut},
    collections::HashMap,
    rc::Rc,
};

use crate::{
    ast::{self, token::IntegerBase, Literal},
    errors::RayResult,
    hir, lir, sema, sym,
    typing::ty::Ty,
};

impl lir::Program {
    pub fn gen(path: ast::Path, root: hir::HirNode) -> RayResult<lir::Program> {
        let mut prog = lir::Program::new(path);
        prog.main = 0;
        prog.funcs.push(lir::Func::new(
            "main",
            Ty::Func(vec![], Box::new(Ty::unit())),
        ));
        let prog = Rc::new(RefCell::new(prog));
        let mut ctx = GenCtx::new(Rc::clone(&prog));
        let (mut inst, _) = root.lir_gen(&mut ctx)?;
        inst.push(lir::InstKind::Return(lir::Value::Empty).into());
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
        let funcs = mr.monomorphize();
        self.funcs.extend(funcs);
    }
}

pub trait LirGen<T> {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<T>;
}

#[derive(Clone, Debug)]
pub struct GenCtx {
    prog: Rc<RefCell<lir::Program>>,
    fx: usize,
    fn_idx: HashMap<String, usize>,
    module_cache: HashMap<String, sym::Symbol>,
    vars: HashMap<String, usize>,
}

impl GenCtx {
    fn new(prog: Rc<RefCell<lir::Program>>) -> GenCtx {
        GenCtx {
            prog,
            fx: 0,
            fn_idx: HashMap::new(),
            module_cache: HashMap::new(),
            vars: HashMap::new(),
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

        prog.funcs.push(lir::Func::new(name, ty));
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
            ty: lir::FnType::from(ty),
            is_c: true,
        });
    }

    fn new_poly_fn_ref(&mut self, name: String, callee_ty: Ty) {
        let mut prog = self.prog.borrow_mut();
        let f = prog.poly_fn_map.get(&name).unwrap();
        let fun = prog.funcs.get(*f).unwrap();
        let poly_ty = fun.ty.clone();

        prog.poly_fn_refs.push(lir::PolyFnRef {
            name,
            // fn_ctx: self.fx,
            poly_ty,
            callee_ty: lir::FnType::from(callee_ty),
        });
    }

    fn get_or_set_local(&mut self, value: lir::Value, ty: Ty, inst: &mut Vec<lir::Inst>) -> usize {
        if let lir::Value::Atom(lir::Atom::Variable(lir::Variable::Local(idx))) = value {
            idx
        } else {
            let (idx, _) = self.new_loc(ty.clone());
            inst.push(lir::InstKind::SetLocal(idx, value.clone()).into());
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

pub type GenResult = (Vec<lir::Inst>, lir::Value);

impl LirGen<GenResult> for (&hir::HirNode, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<GenResult> {
        let &(n, t) = self;
        Ok(match &n.kind {
            hir::HirNodeKind::Var(v) => {
                if let Some(loc) = ctx.vars.get(v) {
                    (vec![], lir::Value::new(lir::Variable::Local(*loc)))
                } else {
                    let (idx, _) = ctx.new_var(v.clone(), t.clone());
                    (vec![], lir::Value::new(lir::Variable::Local(idx)))
                }
            }
            hir::HirNodeKind::Literal(lit) => return (lit, t).lir_gen(ctx),
            hir::HirNodeKind::Type(t) => todo!(),
            hir::HirNodeKind::Cast(ex, ty) => todo!(),
            hir::HirNodeKind::Decl(dec) => todo!(),
            hir::HirNodeKind::Struct(name, fields) => todo!(),
            hir::HirNodeKind::Block(stmts) => {
                let (insts, mut vals): (Vec<_>, Vec<_>) = stmts.lir_gen(ctx)?.into_iter().unzip();
                let inst = insts.concat();
                (inst, vals.pop().unwrap_or_else(|| lir::Value::Empty))
            }
            hir::HirNodeKind::Let(decls, body) => {
                let mut inst = decls
                    .lir_gen(ctx)?
                    .into_iter()
                    .flat_map(|(i, _)| i)
                    .collect::<Vec<_>>();
                let (body_inst, val) = body.lir_gen(ctx)?;
                inst.extend(body_inst);
                (inst, val)
            }
            hir::HirNodeKind::Fun(params, body) => todo!(),
            hir::HirNodeKind::Apply(fun, args) => {
                let fn_ty = fun.get_type();
                let mut inst = vec![];
                let mut arg_vals: Vec<lir::Atom> = vec![];
                for arg in args.iter() {
                    let arg_ty = arg.get_type();
                    let (arg_inst, arg_val) = arg.lir_gen(ctx)?;
                    inst.extend(arg_inst);
                    let arg_loc = ctx.get_or_set_local(arg_val, arg_ty, &mut inst);
                    arg_vals.push(lir::Variable::Local(arg_loc).into());
                }

                let val = if let Some(fn_name) = fun.fn_name() {
                    if ctx.is_poly_func(fn_name) {
                        ctx.new_poly_fn_ref(fn_name.clone(), fn_ty.clone());
                    }

                    lir::Call::new(fn_name.clone(), arg_vals, fn_ty.clone())
                } else {
                    let (mut inst, val) = fun.lir_gen(ctx)?;
                    let fun_loc = ctx.get_or_set_local(val, fn_ty.clone(), &mut inst);
                    lir::Call::new_ref(fun_loc, arg_vals, fn_ty.clone())
                };

                let idx = ctx.get_or_set_local(val, fn_ty, &mut inst);
                (inst, lir::Variable::Local(idx).into())
            }
            hir::HirNodeKind::Typed(t) => return t.get_expr().lir_gen(ctx),
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

impl LirGen<GenResult> for hir::HirNode {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<GenResult> {
        if let hir::HirNodeKind::Typed(t) = &self.kind {
            let n = t.get_expr();
            let t = t.get_type();
            (n, &t).lir_gen(ctx)
        } else {
            unreachable!("unexpected untyped HirNode: {}", self)
        }
    }
}

impl LirGen<GenResult> for hir::HirDecl {
    fn lir_gen(&self, ctx: &mut GenCtx) -> RayResult<GenResult> {
        Ok(match &self.kind {
            hir::HirDeclKind::Pattern(p, d) => match p {
                hir::HirPattern::Var(name) => {
                    if let Some((ex, ty)) = d.borrow_typed() {
                        if let hir::HirNodeKind::Fun(params, body) = &ex.kind {
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
                            if !ret_ty.is_unit() {
                                let body_loc =
                                    ctx.get_or_set_local(body_val, body.get_type(), &mut inst);
                                inst.push(
                                    lir::InstKind::Return(lir::Variable::Local(body_loc).into())
                                        .into(),
                                );
                            } else {
                                inst.push(lir::InstKind::Return(lir::Value::Empty).into());
                            }

                            let mut func = ctx.borrow_func_mut();
                            func.body.instructions = inst;
                            return Ok((vec![], lir::Value::Empty));
                        }
                    }

                    let (mut inst, val) = d.lir_gen(ctx)?;
                    let ty = d.get_type();
                    let src = ctx.get_or_set_local(val, ty.clone(), &mut inst);
                    let (dst, size) = ctx.new_var(name.clone(), ty);
                    inst.push(
                        lir::InstKind::SetLocal(
                            dst,
                            lir::Load {
                                src: lir::Variable::Local(src),
                                offset: lir::Size::zero(),
                                size,
                            }
                            .into(),
                        )
                        .into(),
                    );
                    (inst, lir::Value::new(lir::Variable::Local(dst)))
                }
            },
            hir::HirDeclKind::Type(name, ty) => {
                ctx.new_extern(name.clone(), ty.clone());
                (vec![], lir::Value::Empty)
            }
        })
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

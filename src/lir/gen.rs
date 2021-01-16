use crate::{ast, span::Source};
use crate::{ast::token::IntegerBase, sym};
use crate::{ast::Literal, pathlib::FilePath};
use crate::{
    errors::{RayError, RayErrorKind, RayResult},
    hir,
};
use crate::{lir, typing::ty::Ty};

use std::collections::HashMap;

impl lir::Program {
    pub fn gen(&mut self, root: hir::HirNode) -> RayResult<()> {
        let main = lir::Func {
            name: str!("main"),
            params: vec![],
            locals: vec![],
            ty: lir::FunctionType::from(Ty::Func(vec![], Box::new(Ty::unit()))),
            body: lir::Block::new(),
            symbols: lir::SymbolSet::new(),
        };

        self.funcs.push(main);
        self.main = 0;
        let mut ctx = GenCtx::new(self);
        let (inst, _) = root.lir_gen(&mut ctx)?;
        self.funcs
            .get_mut(0)
            .unwrap()
            .body
            .instructions
            .extend(inst);

        Ok(())
    }
}

pub trait LirGen<'a, T> {
    fn lir_gen(&self, ctx: &mut GenCtx<'a>) -> RayResult<T>;
}

#[derive(Debug)]
pub struct GenCtx<'a> {
    prog: &'a mut lir::Program,
    fx: usize,
    fn_idx: HashMap<String, usize>,
    module_cache: HashMap<String, sym::Symbol>,
    vars: HashMap<String, usize>,
}

impl<'a> GenCtx<'a> {
    fn new(prog: &'a mut lir::Program) -> GenCtx<'a> {
        GenCtx {
            prog,
            fx: 0,
            fn_idx: HashMap::new(),
            module_cache: HashMap::new(),
            vars: HashMap::new(),
        }
    }

    fn new_loc(&mut self, ty: Ty) -> (usize, lir::Size) {
        let func = self.prog.funcs.get_mut(self.fx).unwrap();
        let idx = func.locals.len();
        let size = GenCtx::size_of(&ty);
        let loc = lir::Local::new(idx, ty);
        func.locals.push(loc);
        (idx, size)
    }

    fn new_var(&mut self, v: String, ty: Ty) -> (usize, lir::Size) {
        let (idx, size) = self.new_loc(ty);
        self.vars.insert(v, idx);
        (idx, size)
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

impl LirGen<'_, GenResult> for (&hir::HirNode, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>) -> RayResult<GenResult> {
        let &(n, t) = self;
        match &n.kind {
            hir::HirNodeKind::Var(v) => Ok(if let Some(loc) = ctx.vars.get(v) {
                (vec![], lir::Value::new(lir::Variable::Local(*loc)))
            } else {
                let (idx, _) = ctx.new_var(v.clone(), t.clone());
                (vec![], lir::Value::new(lir::Variable::Local(idx)))
            }),
            hir::HirNodeKind::Literal(lit) => (lit, t).lir_gen(ctx),
            hir::HirNodeKind::Type(t) => todo!(),
            hir::HirNodeKind::Cast(ex, ty) => todo!(),
            hir::HirNodeKind::Decl(dec) => todo!(),
            hir::HirNodeKind::Struct(name, fields) => todo!(),
            hir::HirNodeKind::Block(stmts) => todo!(),
            hir::HirNodeKind::Let(decls, body) => todo!(),
            hir::HirNodeKind::Fun(params, body) => todo!(),
            hir::HirNodeKind::Apply(fun, args) => todo!(),
            hir::HirNodeKind::Typed(t) => t.get_expr().lir_gen(ctx),
        }
    }
}

impl LirGen<'_, GenResult> for (&Literal, &Ty) {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>) -> RayResult<GenResult> {
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

impl LirGen<'_, GenResult> for hir::HirNode {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>) -> RayResult<GenResult> {
        if let hir::HirNodeKind::Typed(t) = &self.kind {
            let n = t.get_expr();
            let t = t.get_type();
            (n, &t).lir_gen(ctx)
        } else {
            unreachable!("unexpected untyped HirNode: {}", self)
        }
    }
}

impl LirGen<'_, GenResult> for hir::HirDecl {
    fn lir_gen(&self, ctx: &mut GenCtx<'_>) -> RayResult<GenResult> {
        match &self.kind {
            hir::HirDeclKind::Pattern(p, d) => match p {
                hir::HirPattern::Var(v) => {
                    let (mut inst, val) = d.lir_gen(ctx)?;
                    let ty = d.get_type();
                    let src = ctx.get_or_set_local(val, ty.clone(), &mut inst);
                    let (dst, size) = ctx.new_var(v.clone(), ty);
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
                    Ok((inst, lir::Value::new(lir::Variable::Local(dst))))
                }
            },
            hir::HirDeclKind::Type(n, t) => todo!(),
        }
    }
}

impl<'a, T> LirGen<'a, Vec<GenResult>> for Vec<T>
where
    T: LirGen<'a, GenResult>,
{
    fn lir_gen(&self, ctx: &mut GenCtx<'a>) -> RayResult<Vec<GenResult>> {
        self.iter()
            .map(|t| t.lir_gen(ctx))
            .collect::<RayResult<Vec<_>>>()
    }
}

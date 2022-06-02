use std::collections::HashSet;

use crate::{
    ast::{
        asm::Asm, Assign, BinOp, Block, Call, Cast, Closure, Curly, Decl, Dot, Expr, Extern, For,
        Func, FuncSig, If, Impl, Index, List, Literal, Loop, Module, Name, New, Node, Path,
        Pattern, Range, Sequence, Struct, Trait, Tuple, UnaryOp, While,
    },
    span::{parsed::Parsed, SourceMap},
};

use super::{
    state::TyEnv,
    ty::{Ty, TyVar},
    ApplySubst, ApplySubstMut, Subst, TyCtx, TypeError,
};

pub type TypeCheckResult<T = ()> = Result<T, TypeError>;

#[derive(Debug, Clone, Default)]
pub struct CheckCtx {
    tyvars: HashSet<TyVar>,
}

#[derive(Debug)]
pub struct TypeCheckSystem<'a> {
    tcx: &'a mut TyCtx,
    srcmap: &'a SourceMap,
}

impl<'a> TypeCheckSystem<'a> {
    pub fn new(tcx: &'a mut TyCtx, srcmap: &'a SourceMap) -> Self {
        TypeCheckSystem { tcx, srcmap }
    }

    pub fn type_check<T, U>(&mut self, v: &mut T) -> TypeCheckResult<U>
    where
        T: TypeCheck<Output = U>,
    {
        let mut kcx = CheckCtx::default();
        v.type_check(self.tcx, self.srcmap, &mut kcx, None)
    }
}

pub trait TypeCheck {
    type Output;

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult<Self::Output>;
}

impl<'a, T, U> TypeCheck for T
where
    T: Iterator<Item = &'a mut U>,
    U: TypeCheck + 'a,
{
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        for value in self {
            value.type_check(ctx, srcmap, kcx, None)?;
        }

        Ok(())
    }
}

impl TypeCheck for Module<(), Decl> {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        self.decls.iter_mut().type_check(ctx, srcmap, kcx, None)
    }
}

impl<T, U> TypeCheck for Node<T>
where
    T: TypeCheck<Output = U> + std::fmt::Display,
{
    type Output = U;

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        _: Option<&mut Ty>,
    ) -> TypeCheckResult<U> {
        let mut ty = ctx.maybe_ty_of(self.id).cloned();
        if let Some(ty) = &ty {
            log::debug!("{}: {}", self.value, ty);
        }
        let result = match self.value.type_check(ctx, srcmap, kcx, ty.as_mut()) {
            Ok(u) => u,
            Err(mut err) => {
                let src = srcmap.get(self);
                err.src.push(src);
                return Err(err);
            }
        };

        if let Some(ty) = ty {
            ctx.set_ty(self.id, ty);
        }

        Ok(result)
    }
}

// impl<T> TypeCheck for Node<T>
// where
//     T: TypeCheck<Output = Subst> + ApplySubst,
// {
//     type Output = ();

//     fn type_check(&mut self, ctx: &mut TyCtx, srcmap: &SourceMap, kcx: &mut Fcx, _: Option<Ty>) -> TypeCheckResult {
//         let ty = ctx.maybe_ty_of(self.id).cloned();
//         let subst = self.value.type_check(ctx, srcmap, kcx, ty)?;
//         self.value.apply_subst_mut(&subst);
//         Ok(())
//     }
// }

impl TypeCheck for Expr {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        match self {
            Expr::Assign(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Asm(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::BinOp(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Block(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Break(ex) => Ok(()), // ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Call(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Cast(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Closure(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Curly(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::DefaultValue(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Dot(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Func(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::For(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::If(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Index(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Labeled(lhs, rhs) => {
                lhs.type_check(ctx, srcmap, kcx, None)?;
                rhs.type_check(ctx, srcmap, kcx, None)
            }
            Expr::List(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Literal(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Loop(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Name(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::New(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Path(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Pattern(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Paren(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Range(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Return(ex) => Ok(()), // ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Sequence(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Tuple(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Type(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::TypeAnnotated(ex, tys) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::UnaryOp(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::Unsafe(ex) => ex.type_check(ctx, srcmap, kcx, ty),
            Expr::While(ex) => ex.type_check(ctx, srcmap, kcx, ty),
        }
    }
}

impl TypeCheck for Decl {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        match self {
            Decl::Extern(decl) => decl.type_check(ctx, srcmap, kcx, ty),
            Decl::Mutable(decl) => decl.type_check(ctx, srcmap, kcx, ty),
            Decl::Name(decl) => decl.type_check(ctx, srcmap, kcx, ty),
            Decl::Declare(decl) => decl.type_check(ctx, srcmap, kcx, ty),
            Decl::Func(decl) => decl.type_check(ctx, srcmap, kcx, ty),
            Decl::FnSig(decl) => decl.type_check(ctx, srcmap, kcx, ty),
            Decl::Struct(decl) => decl.type_check(ctx, srcmap, kcx, ty),
            Decl::Trait(decl) => decl.type_check(ctx, srcmap, kcx, ty),
            Decl::TypeAlias(decl, _) => decl.type_check(ctx, srcmap, kcx, ty),
            Decl::Impl(decl) => decl.type_check(ctx, srcmap, kcx, ty),
        }
    }
}

impl TypeCheck for Extern {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        self.decl_mut().type_check(ctx, srcmap, kcx, None)
    }
}

impl TypeCheck for Func {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        let (fn_ty, subst) = if let Some(ty) = &ty {
            // TODO: this is pretty ugly, is there a better way?
            (**ty).clone().formalize(&self.sig.path, &kcx.tyvars)
        } else {
            panic!("function does not have a type")
        };
        log::debug!("function type formalized: {}", fn_ty);

        if let (Some(ty_params), ..) = fn_ty.try_borrow_fn()? {
            kcx.tyvars.extend(ty_params.iter().cloned());
        }

        ctx.apply_subst_mut(&subst);

        if let Some(body) = &mut self.body {
            body.type_check(ctx, srcmap, kcx, None)?;
        }

        if let Some(ty) = ty {
            *ty = fn_ty;
        }

        kcx.tyvars.clear();
        Ok(())
    }
}

impl TypeCheck for FuncSig {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Struct {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Trait {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Impl {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Assign {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        self.lhs.type_check(ctx, srcmap, kcx, None)?;
        self.rhs.type_check(ctx, srcmap, kcx, None)?;

        let lhs_ty = ctx.ty_of(self.lhs.id);
        let rhs_ty = ctx.ty_of(self.rhs.id);
        if lhs_ty != rhs_ty {
            return Err(TypeError::equality(lhs_ty, rhs_ty));
        }

        Ok(())
    }
}

impl TypeCheck for Asm {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for BinOp {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        _: Option<&mut Ty>,
    ) -> TypeCheckResult {
        self.lhs.type_check(ctx, srcmap, kcx, None)?;
        self.rhs.type_check(ctx, srcmap, kcx, None)?;
        Ok(())
    }
}

impl TypeCheck for Block {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        self.stmts.iter_mut().type_check(ctx, srcmap, kcx, None)
    }
}

impl TypeCheck for Call {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        self.callee.type_check(ctx, srcmap, kcx, None)?;
        self.args.type_check(ctx, srcmap, kcx, None)?;

        Ok(())
    }
}

impl TypeCheck for Cast {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Closure {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Curly {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Dot {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for For {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for If {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Index {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for List {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Literal {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Loop {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Name {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for New {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Path {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Pattern {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Range {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Sequence {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Tuple {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for Parsed<Ty> {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for UnaryOp {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

impl TypeCheck for While {
    type Output = ();

    fn type_check(
        &mut self,
        ctx: &mut TyCtx,
        srcmap: &SourceMap,
        kcx: &mut CheckCtx,
        ty: Option<&mut Ty>,
    ) -> TypeCheckResult {
        Ok(())
    }
}

use std::ops::DerefMut;

use top::solver::SolveResult;

use crate::{
    ast::{Decl, Func, Module, Node, Path},
    typing::{
        TyCtx,
        info::TypeSystemInfo,
        ty::{Ty, TyVar},
    },
};

pub trait ApplySolution {
    type Ctx;

    fn apply_solution(
        &mut self,
        solution: &SolveResult<TypeSystemInfo, Ty, TyVar>,
        tcx: &TyCtx,
        ctx: &Self::Ctx,
    );
}

impl<T, Ctx> ApplySolution for Vec<T>
where
    T: ApplySolution<Ctx = Ctx>,
{
    type Ctx = Ctx;

    fn apply_solution(
        &mut self,
        solution: &SolveResult<TypeSystemInfo, Ty, TyVar>,
        tcx: &TyCtx,
        ctx: &Self::Ctx,
    ) {
        for t in self {
            t.apply_solution(solution, tcx, ctx);
        }
    }
}

impl<T, Ctx> ApplySolution for Node<T>
where
    T: ApplySolution<Ctx = Ctx>,
{
    type Ctx = Ctx;

    fn apply_solution(
        &mut self,
        solution: &SolveResult<TypeSystemInfo, Ty, TyVar>,
        tcx: &TyCtx,
        ctx: &Self::Ctx,
    ) {
        self.deref_mut().apply_solution(solution, tcx, ctx);
    }
}

impl ApplySolution for Module<(), Decl> {
    type Ctx = ();

    fn apply_solution(
        &mut self,
        solution: &SolveResult<TypeSystemInfo, Ty, TyVar>,
        tcx: &TyCtx,
        ctx: &Self::Ctx,
    ) {
        todo!()
    }
}

impl ApplySolution for Decl {
    type Ctx = ();

    fn apply_solution(
        &mut self,
        solution: &SolveResult<TypeSystemInfo, Ty, TyVar>,
        tcx: &TyCtx,
        ctx: &Self::Ctx,
    ) {
        match self {
            Decl::Extern(ext) => todo!(),
            Decl::Mutable(_) => todo!(),
            Decl::Name(_) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::Func(func) => func.apply_solution(solution, tcx, &None),
            Decl::FnSig(_) => todo!(),
            Decl::Struct(_) => todo!(),
            Decl::Trait(tr) => {
                let trait_path = tr.ty.get_path().unwrap();
                todo!();
            }
            Decl::TypeAlias(_, _) => todo!(),
            Decl::Impl(imp) => {
                let impl_path = if imp.is_object {
                    None
                } else {
                    Some(imp.ty.get_path().unwrap())
                };

                if let Some(funcs) = &mut imp.funcs {
                    funcs.apply_solution(solution, tcx, &impl_path);
                }
            }
        }
    }
}

impl ApplySolution for Func {
    type Ctx = Option<Path>;

    fn apply_solution(
        &mut self,
        solution: &SolveResult<TypeSystemInfo, Ty, TyVar>,
        tcx: &TyCtx,
        ctx: &Self::Ctx,
    ) {
        todo!()
    }
}

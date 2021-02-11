use itertools::Itertools;

use std::collections::{HashMap, VecDeque};

use crate::{
    ast::{Decl, Expr, HasSource, Module, Node, Path, SourceInfo, TypeParams},
    errors::{RayError, RayErrorKind, RayResult},
    pathlib::FilePath,
    span::Source,
    typing::{
        info::TypeInfo,
        traits::HasType,
        ty::{Ty, TyVar},
        ApplySubst, Subst, TyCtx,
    },
};

mod collect;
mod convert_decl;
mod convert_expr;
mod node;
pub use collect::*;
pub use convert_decl::*;
pub use convert_expr::*;
pub use node::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HirInfo {
    src_info: SourceInfo,
    ty_info: TypeInfo,
}

impl HasSource for HirInfo {
    fn src(&self) -> Source {
        self.src_info.src()
    }

    fn set_src(&mut self, src: Source) {
        self.src_info.set_src(src)
    }
}

impl HasType for HirInfo {
    fn ty(&self) -> Ty {
        self.ty_info.ty()
    }
}

impl ApplySubst for HirInfo {
    fn apply_subst(self, subst: &Subst) -> Self {
        HirInfo {
            src_info: self.src_info.apply_subst(subst),
            ty_info: self.ty_info.apply_subst(subst),
        }
    }
}

impl HirInfo {
    pub fn path(&self) -> &Path {
        &self.src_info.path
    }

    pub fn src_info(&self) -> &SourceInfo {
        &self.src_info
    }

    pub fn original_ty(&self) -> &Ty {
        self.ty_info.original_ty()
    }
}

type SourceModule = Module<Expr<SourceInfo>, Decl<SourceInfo>, SourceInfo>;
type HirModule = Module<HirNode<SourceInfo>, HirDecl<SourceInfo>, SourceInfo>;

pub fn transform_modules(
    module_path: &Path,
    modules: &HashMap<Path, SourceModule>,
    ctx: &mut TyCtx,
) -> Result<HirModule, RayError> {
    let module = modules.get(module_path).unwrap();
    let (stmts, decls) = get_root(module, modules, ctx)?;
    let mut module = Module::new_from(module);
    module.stmts = stmts;
    module.decls = decls;
    Ok(module)
}

fn get_root(
    module: &SourceModule,
    modules: &HashMap<Path, SourceModule>,
    ctx: &mut TyCtx,
) -> Result<
    (
        Vec<Node<HirNode<SourceInfo>, SourceInfo>>,
        Vec<Node<HirDecl<SourceInfo>, SourceInfo>>,
    ),
    RayError,
> {
    let (stmts, decls) = collect(module, modules, ctx)?;
    let mut stmts: VecDeque<_> = stmts.into();
    let mut nodes = vec![];
    if stmts.len() != 0 {
        loop {
            let ex = stmts.pop_front().unwrap();
            let id = ex.id;
            let info = ex.info.clone();
            let node = ex.to_hir_node_with(&mut stmts, &module.path, id, &info, ctx)?;
            nodes.push(node);
            if stmts.len() == 0 {
                break;
            }
        }
    }

    Ok((nodes, decls))
}

fn collect(
    module: &SourceModule,
    modules: &HashMap<Path, SourceModule>,
    ctx: &mut TyCtx,
) -> Result<
    (
        Vec<Node<Expr<SourceInfo>, SourceInfo>>,
        Vec<Node<HirDecl<SourceInfo>, SourceInfo>>,
    ),
    RayError,
> {
    let mut stmts = vec![];
    let mut decls = vec![];
    for import_path in module.imports.iter() {
        let imported_module = modules.get(import_path).unwrap();
        let (imported_stmts, imported_decls) = collect(imported_module, modules, ctx)?;
        decls.extend(imported_decls);
        stmts.extend(imported_stmts);
    }

    decls.extend(collect_decls(module, ctx)?);
    stmts.extend(module.stmts.clone());
    Ok((stmts, decls))
}

fn collect_decls(
    module: &SourceModule,
    ctx: &mut TyCtx,
) -> RayResult<Vec<Node<HirDecl<SourceInfo>, SourceInfo>>> {
    let mut decls = vec![];
    // sorting it by kind will allow a certain order to the collection
    for decl in module.decls.iter().sorted_by_key(|d| &d.value) {
        decls.extend(decl.to_hir_decl(false, ctx)?);
    }

    Ok(decls)
}

fn get_ty_vars(
    ty_params: Option<&TypeParams>,
    scope: &Path,
    filepath: &FilePath,
    ctx: &mut TyCtx,
) -> Result<Vec<TyVar>, RayError> {
    let mut ty_vars = vec![];
    if let Some(ty_params) = ty_params {
        for tp in ty_params.tys.iter() {
            let ty = tp.clone_value().from_ast_ty(scope, ctx);
            if let Ty::Var(v) = ty {
                ty_vars.push(v.clone());
            } else {
                return Err(RayError {
                    msg: format!("expected type parameter, but found `{}`", tp),
                    src: vec![Source {
                        span: tp.span().copied(),
                        filepath: filepath.clone(),
                    }],
                    kind: RayErrorKind::Type,
                });
            }
        }
    }

    Ok(ty_vars)
}

pub trait IntoHirNode<Info>
where
    Self: Sized,
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    type Output;

    #[inline(always)]
    fn to_hir_node(
        self,
        scope: &Path,
        id: u64,
        info: &Info,
        ctx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        let mut deq = VecDeque::new();
        self.to_hir_node_with(&mut deq, scope, id, info, ctx)
    }

    fn to_hir_node_with(
        self,
        rest: &mut VecDeque<Node<Expr<Info>, Info>>,
        scope: &Path,
        id: u64,
        info: &Info,
        ctx: &mut TyCtx,
    ) -> RayResult<Self::Output>;
}

impl IntoHirNode<SourceInfo> for Vec<Node<Expr<SourceInfo>, SourceInfo>> {
    type Output = Vec<Node<HirNode<SourceInfo>, SourceInfo>>;

    fn to_hir_node_with(
        self,
        _: &mut VecDeque<Node<Expr<SourceInfo>, SourceInfo>>,
        scope: &Path,
        id: u64,
        info: &SourceInfo,
        ctx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        self.into_iter()
            .map(|e| e.to_hir_node(scope, id, info, ctx))
            .collect()
    }
}

pub trait IntoHirDecl<Info>
where
    Self: Sized,
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    type Output;

    fn to_hir_decl(self, is_extern: bool, ctx: &mut TyCtx) -> RayResult<Self::Output>;
}

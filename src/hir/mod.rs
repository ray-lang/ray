use itertools::Itertools;

use std::collections::{HashMap, VecDeque};

use crate::{
    ast::{
        self, Decl, Expr, HasSource, Literal, LowerAST, Module, Node, Path, SourceInfo, TypeParams,
    },
    errors::{RayError, RayErrorKind, RayResult},
    pathlib::FilePath,
    span::{Source, SourceMap, Span},
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
    pub fn new(src: SourceInfo, ty: Ty) -> Self {
        Self {
            src_info: src,
            ty_info: TypeInfo::new(ty),
        }
    }

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

type SourceModule = Module<Expr, Decl>;

pub fn transform_modules(
    module_path: &Path,
    modules: &mut HashMap<Path, SourceModule>,
    srcmaps: &mut HashMap<Path, SourceMap>,
    tcx: &mut TyCtx,
) -> Result<(SourceModule, SourceMap), RayError> {
    let module = modules.remove(module_path).unwrap();
    let mut srcmap = srcmaps.remove(module_path).unwrap();
    let mut new_module = Module::new_from(&module);
    let (mut stmts, mut decls) = get_root(module, &mut srcmap, modules, srcmaps, tcx)?;

    let filepath = new_module.root_filepath.clone();

    let mut span = Span::new();
    if let Some(first) = stmts.first() {
        span.start = srcmap.span_of(first).start;
    }

    if let Some(last) = stmts.last() {
        span.end = srcmap.span_of(last).end;
    }

    let end_node = Node::new(Expr::Literal(Literal::Unit));
    srcmap.set_src(
        &end_node,
        Source {
            filepath: filepath.clone(),
            ..Default::default()
        },
    );
    stmts.push(end_node);

    let body = Node::new(Expr::Block(ast::Block {
        stmts,
        is_top_level: true,
    }));
    srcmap.set_src(&body, Source::new(filepath.clone(), span, Path::new()));

    // create a main function for the stmts
    let main_decl = Node::new(Decl::Fn(ast::Fn::new(Path::from("main"), vec![], body)));
    srcmap.set_src(&main_decl, Source::new(filepath.clone(), span, Path::new()));
    decls.insert(0, main_decl);

    new_module.decls = decls;
    Ok((new_module, srcmap))
}

fn get_root(
    module: SourceModule,
    srcmap: &mut SourceMap,
    modules: &mut HashMap<Path, SourceModule>,
    srcmaps: &mut HashMap<Path, SourceMap>,
    tcx: &mut TyCtx,
) -> Result<(Vec<Node<Expr>>, Vec<Node<Decl>>), RayError> {
    let (mut stmts, mut decls) = collect(module, srcmap, modules, srcmaps, tcx)?;
    for stmt in stmts.iter_mut() {
        stmt.lower(srcmap, tcx)?;
    }

    // sorting it by kind will allow a certain order to the collection
    decls.sort();
    Ok((stmts, decls))
}

fn collect(
    mut module: SourceModule,
    srcmap: &mut SourceMap,
    modules: &mut HashMap<Path, SourceModule>,
    srcmaps: &mut HashMap<Path, SourceMap>,
    tcx: &mut TyCtx,
) -> Result<(Vec<Node<Expr>>, Vec<Node<Decl>>), RayError> {
    let mut stmts = vec![];
    let mut decls = vec![];
    for import_path in module.imports.iter() {
        let imported_module = modules.remove(import_path).unwrap();
        let mut imported_srcmap = srcmaps.remove(import_path).unwrap();
        let (imported_stmts, imported_decls) =
            collect(imported_module, &mut imported_srcmap, modules, srcmaps, tcx)?;
        srcmap.extend(imported_srcmap);
        decls.extend(imported_decls);
        stmts.extend(imported_stmts);
    }

    for decl in module.decls.iter_mut() {
        decl.lower(srcmap, tcx)?;
    }

    decls.extend(module.decls);
    stmts.extend(module.stmts.clone());
    Ok((stmts, decls))
}

// pub trait IntoHirNode
// where
//     Self: Sized,
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     type Output;

//     #[inline(always)]
//     fn to_hir_node(
//         self,
//         scope: &Path,
//         id: u64,
//         info: &Info,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         let mut deq = VecDeque::new();
//         self.to_hir_node_with(&mut deq, scope, id, info, ctx)
//     }

//     fn to_hir_node_with(
//         self,
//         rest: &mut VecDeque<Node<Expr>,
//         scope: &Path,
//         id: u64,
//         info: &Info,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output>;
// }

// impl IntoHirNode for Vec<Node<Expr, SourceInfo>> {
//     type Output = Vec<Node<HirNode>;

//     fn to_hir_node_with(
//         self,
//         _: &mut VecDeque<Node<Expr>,
//         scope: &Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         self.into_iter()
//             .map(|e| e.to_hir_node(scope, id, info, ctx))
//             .collect()
//     }
// }

// pub trait IntoHirDecl
// where
//     Self: Sized,
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     type Output;

//     fn to_hir_decl(self, is_extern: bool, ctx: &mut TyCtx) -> RayResult<Self::Output>;
// }

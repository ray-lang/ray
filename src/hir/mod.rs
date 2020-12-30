use std::collections::HashMap;

use crate::{
    ast::{Decl, DeclKind, Expr, ExprKind, Module, Path, TypeKind, TypeParams},
    errors::{RayError, RayErrorKind, RayResult},
    pathlib::FilePath,
    span::Span,
    typing::{
        ty::{Ty, TyVar},
        Ctx,
    },
};

mod convert;
mod node;
pub use convert::*;
pub use node::*;

#[derive(Clone, Debug)]
pub struct HirModule {
    pub root: HirNode<Span>,
}

impl HirModule {
    pub fn from_ast_module(
        module_path: &Path,
        modules: &HashMap<Path, Module>,
        ctx: &mut Ctx,
    ) -> Result<HirModule, RayError> {
        let module = modules.get(module_path).unwrap();
        let root = HirModule::get_root(module, modules, ctx)?;
        Ok(HirModule { root })
    }

    fn get_root(
        module: &Module,
        modules: &HashMap<Path, Module>,
        ctx: &mut Ctx,
    ) -> Result<HirNode<Span>, RayError> {
        let stmts = HirModule::collect(module, modules, ctx)?;
        Ok(if let Some((first, rest)) = stmts.split_first() {
            first.to_hir_node_with(rest, &module.path, &first.filepath, ctx)?
        } else {
            HirNodeKind::Const(Ty::unit()).into()
        })
    }

    fn collect(
        module: &Module,
        modules: &HashMap<Path, Module>,
        ctx: &mut Ctx,
    ) -> Result<Vec<Expr>, RayError> {
        let mut stmts = vec![];
        for import_path in module.imports.iter() {
            let imported_module = modules.get(import_path).unwrap();
            let imported_stmts = HirModule::collect(imported_module, modules, ctx)?;
            stmts.extend(imported_stmts);
        }

        HirModule::collect_decls(module, ctx)?;
        stmts.extend(module.stmts.clone());
        Ok(stmts)
    }

    fn collect_decls(module: &Module, ctx: &mut Ctx) -> Result<(), RayError> {
        for decl in module.decls.iter() {
            HirModule::decl_to_type(&module.path, decl, ctx)?;
        }

        // let mut funcs = vec![];
        // for stmt in module.stmts.iter() {
        //     if let ExprKind::Fn(func) = &stmt.kind {
        //         let node = func.to_hir_node(&module.path, &stmt.filepath, ctx)?;
        //         let fn_name = func.sig.name.clone().ok_or_else(|| RayError {
        //             msg: format!("externed function must have a name"),
        //             span: Some(stmt.span),
        //             fp: stmt.filepath.clone(),
        //             kind: RayErrorKind::Type,
        //         })?;
        //         funcs.push((fn_name, node));
        //     }
        // }

        Ok(())
    }

    fn get_ty_vars(
        ty_params: Option<&TypeParams>,
        scope: &Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> Result<Vec<TyVar>, RayError> {
        let mut ty_vars = vec![];
        if let Some(ty_params) = ty_params {
            for tp in ty_params.tys.iter() {
                match &tp.kind {
                    TypeKind::Generic { name, .. } => {
                        let fqn = scope.append(name);
                        let tv = TyVar(fqn.to_string());
                        ctx.bind_var(name.to_string(), Ty::Var(tv.clone()));
                        ty_vars.push(tv);
                    }
                    _ => {
                        return Err(RayError {
                            msg: format!("expected type parameter, but found `{}`", tp),
                            span: tp.span,
                            fp: filepath.clone(),
                            kind: RayErrorKind::Type,
                        })
                    }
                }
            }
        }

        Ok(ty_vars)
    }

    fn decl_to_type(scope: &Path, decl: &Decl, ctx: &mut Ctx) -> Result<(), RayError> {
        match &decl.kind {
            DeclKind::Extern(decl) => HirModule::decl_to_type(scope, decl, ctx),
            DeclKind::Name(n) => {
                let t = Ty::from_ast_ty(&n.ty.as_ref().unwrap().kind, scope, ctx);
                ctx.bind_var(n.name.clone(), t);
                Ok(())
            }
            DeclKind::Struct(st) => {
                let name = st.name.to_string();
                let struct_scope = scope.append(name.clone());

                let mut struct_ctx = ctx.clone();
                let ty_vars = HirModule::get_ty_vars(
                    st.ty_params.as_ref(),
                    scope,
                    &decl.filepath,
                    &mut struct_ctx,
                )?;

                let mut fields_vec = vec![];
                let mut field_tys = vec![];
                if let Some(fields) = &st.fields {
                    for field in fields.iter() {
                        let ty = if let Some(ty) = &field.ty {
                            Ty::from_ast_ty(&ty.kind, &struct_scope, &struct_ctx)
                        } else {
                            return Err(RayError {
                                msg: format!("struct field on `{}` does not have a type", st.name),
                                span: Some(field.span),
                                fp: decl.filepath.clone(),
                                kind: RayErrorKind::Type,
                            });
                        };

                        fields_vec.push((field.name.clone(), ty.clone()));
                        field_tys.push(ty);
                    }
                }

                let struct_ty = Ty::Projection(
                    name.clone(),
                    ty_vars.iter().map(|t| Ty::Var(t.clone())).collect(),
                );
                ctx.add_struct_ty(name.clone(), fields_vec);

                let fn_ty = Ty::Func(field_tys, Box::new(struct_ty));
                let ty = if ty_vars.len() != 0 {
                    Ty::All(ty_vars, Box::new(fn_ty))
                } else {
                    fn_ty
                };

                ctx.bind_var(format!("{}::init", name), ty);
                Ok(())
            }
            DeclKind::Fn(sig) => {
                let fn_name = sig.name.as_ref().ok_or_else(|| RayError {
                    msg: format!("externed function must have a name"),
                    span: Some(decl.span),
                    fp: decl.filepath.clone(),
                    kind: RayErrorKind::Type,
                })?;

                let fn_scope = scope.append(fn_name);

                let mut fn_ctx = ctx.clone();
                let ty_vars = HirModule::get_ty_vars(
                    sig.ty_params.as_ref(),
                    &fn_scope,
                    &decl.filepath,
                    &mut fn_ctx,
                )?;

                // make sure that the signature is fully typed
                let mut param_tys = vec![];
                for param in sig.params.iter() {
                    if let Some(ty) = &param.ty {
                        param_tys.push(Ty::from_ast_ty(&ty.kind, &fn_scope, &fn_ctx));
                    } else {
                        return Err(RayError {
                            msg: format!(
                                "parameter of externed function {} must have a type annotation",
                                fn_name
                            ),
                            fp: decl.filepath.clone(),
                            kind: RayErrorKind::Type,
                            span: Some(param.span),
                        });
                    }
                }

                let ret_ty = sig
                    .ret_ty
                    .as_ref()
                    .map(|t| Ty::from_ast_ty(&t.kind, &fn_scope, &fn_ctx))
                    .unwrap_or_else(|| Ty::unit());

                let fn_ty = Ty::Func(param_tys, Box::new(ret_ty));
                let ty = if ty_vars.len() != 0 {
                    Ty::All(ty_vars, Box::new(fn_ty))
                } else {
                    fn_ty
                };

                ctx.bind_var(fn_name.clone(), ty);
                Ok(())
            }
            _ => unimplemented!("decl to type: {}", decl),
        }
    }
}

pub trait IntoHirNode {
    #[inline(always)]
    fn to_hir_node(
        &self,
        scope: &Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        self.to_hir_node_with(&[], scope, filepath, ctx)
    }

    fn to_hir_node_with(
        &self,
        rest: &[Expr],
        scope: &Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode<Span>>;
}

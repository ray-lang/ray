use itertools::Itertools;

use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    ast::{Decl, DeclKind, Expr, ExprKind, Module, Path, TypeParams},
    errors::{RayError, RayErrorKind, RayResult},
    pathlib::FilePath,
    span::Source,
    subst,
    typing::{
        predicate::TyPredicate,
        ty::{ImplTy, StructTy, TraitTy, Ty, TyVar},
        ApplySubst, Ctx,
    },
};

mod collect;
mod convert;
mod formalize;
mod node;
pub use collect::*;
pub use convert::*;
pub use formalize::*;
pub use node::*;

#[derive(Clone, Debug)]
pub struct HirModule {
    pub root: HirNode,
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
    ) -> Result<HirNode, RayError> {
        let (decls, stmts) = HirModule::collect(module, modules, ctx)?;
        let mut stmts: VecDeque<_> = stmts.into();
        let mut nodes = vec![];
        if stmts.len() != 0 {
            loop {
                let ex = stmts.pop_front().unwrap();
                let filepath = ex.src.filepath.clone();
                let node = ex.to_hir_node_with(&mut stmts, &module.path, &filepath, ctx)?;
                nodes.push(node);
                if stmts.len() == 0 {
                    break;
                }
            }
        }

        let body = if nodes.len() == 1 {
            nodes.pop().unwrap()
        } else {
            HirNodeKind::Block(nodes).into()
        };

        if decls.len() == 0 {
            return Ok(body);
        }

        Ok(HirNodeKind::Let(decls, Box::new(body)).into())
    }

    fn collect(
        module: &Module,
        modules: &HashMap<Path, Module>,
        ctx: &mut Ctx,
    ) -> Result<(Vec<HirDecl>, Vec<Expr>), RayError> {
        let mut stmts = vec![];
        let mut decls = vec![];
        for import_path in module.imports.iter() {
            let imported_module = modules.get(import_path).unwrap();
            let (imported_decls, imported_stmts) =
                HirModule::collect(imported_module, modules, ctx)?;
            decls.extend(imported_decls);
            stmts.extend(imported_stmts);
        }

        let (d, f) = HirModule::collect_decls(module, ctx)?;
        decls.extend(d);
        stmts.extend(f);
        stmts.extend(module.stmts.clone());
        Ok((decls, stmts))
    }

    fn collect_decls(
        module: &Module,
        ctx: &mut Ctx,
    ) -> Result<(Vec<HirDecl>, Vec<Expr>), RayError> {
        let mut decls = vec![];
        let mut deferred_funcs = vec![];

        // sorting it by kind will allow a certain order to the collection
        for decl in module.decls.iter().sorted_by_key(|d| &d.kind) {
            let (d, f) = HirModule::convert_decl(&module.path, decl, false, ctx)?;
            decls.extend(d);
            deferred_funcs.extend(f);
        }

        Ok((decls, deferred_funcs))
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
                if !tp.kind.is_generic() {
                    return Err(RayError {
                        msg: format!("expected type parameter, but found `{}`", tp),
                        src: vec![Source {
                            span: tp.span,
                            filepath: filepath.clone(),
                        }],
                        kind: RayErrorKind::Type,
                    });
                }

                let ty = Ty::from_ast_ty(&tp.kind, scope, ctx);
                if let Ty::Var(v) = ty {
                    ty_vars.push(v.clone());
                } else {
                    unreachable!("bug: type should be a variable => {:?}", tp)
                }
            }
        }

        Ok(ty_vars)
    }

    fn convert_decl(
        scope: &Path,
        decl: &Decl,
        is_extern: bool,
        ctx: &mut Ctx,
    ) -> Result<(Vec<HirDecl>, Vec<Expr>), RayError> {
        let mut decls = vec![];
        let mut deferred_funcs = vec![];
        match &decl.kind {
            DeclKind::Extern(decl) => return HirModule::convert_decl(scope, decl, true, ctx),
            DeclKind::Name(n) => {
                let name = n.name.clone();
                let ty = Ty::from_ast_ty(&n.ty.as_ref().unwrap().kind, scope, ctx);
                ctx.bind_var(name.clone(), ty.clone());
                decls.push(HirDecl::ty(name, ty).with_src(Some(decl.src.clone())));
            }
            DeclKind::Struct(st) => {
                let name = st.name.to_string();
                let struct_path = scope.append(name.clone());
                let fqn = struct_path.to_string();

                let mut struct_ctx = ctx.clone();
                let ty_vars = HirModule::get_ty_vars(
                    st.ty_params.as_ref(),
                    &struct_path,
                    &decl.src.filepath,
                    &mut struct_ctx,
                )?;

                let mut fields_vec = vec![];
                let mut field_tys = vec![];
                if let Some(fields) = &st.fields {
                    for field in fields.iter() {
                        let ty = if let Some(ty) = &field.ty {
                            Ty::from_ast_ty(&ty.kind, &struct_path, &mut struct_ctx)
                        } else {
                            return Err(RayError {
                                msg: format!("struct field on `{}` does not have a type", st.name),
                                src: vec![Source {
                                    span: Some(field.span),
                                    filepath: decl.src.filepath.clone(),
                                }],
                                kind: RayErrorKind::Type,
                            });
                        };

                        fields_vec.push((field.name.clone(), ty.clone()));
                        field_tys.push(ty);
                    }
                }

                let struct_ty = Ty::Projection(
                    fqn.clone(),
                    ty_vars.iter().map(|t| Ty::Var(t.clone())).collect(),
                    field_tys.clone(),
                );
                ctx.add_struct_ty(
                    name,
                    StructTy {
                        path: struct_path,
                        ty: struct_ty.clone(),
                        fields: fields_vec,
                    },
                );

                let fn_ty = Ty::Func(field_tys, Box::new(struct_ty));
                let ty = if ty_vars.len() != 0 {
                    Ty::All(ty_vars, Box::new(fn_ty))
                } else {
                    fn_ty
                };

                let name = format!("{}::init", fqn);
                ctx.bind_var(name.clone(), ty.clone());
                decls.push(HirDecl::ty(name, ty).with_src(Some(decl.src.clone())));
            }
            DeclKind::Fn(sig) => {
                let name = sig.name.as_ref().ok_or_else(|| RayError {
                    msg: format!("externed function must have a name"),
                    src: vec![decl.src.clone()],
                    kind: RayErrorKind::Type,
                })?;

                let fn_scope = scope.append(name);

                let mut fn_ctx = ctx.clone();

                // make sure that the signature is fully typed
                let ty = Ty::from_sig(sig, &fn_scope, &decl.src.filepath, &mut fn_ctx, ctx)?;
                ctx.bind_var(name.clone(), ty.clone());
                decls.push(HirDecl::ty(name, ty).with_src(Some(decl.src.clone())));
            }
            DeclKind::Trait(tr) => {
                let ty_span = tr.ty.span.unwrap();
                let (name, ty_params) = match Ty::from_ast_ty(&tr.ty.kind, scope, ctx) {
                    Ty::Projection(n, tp, _) => (n, tp),
                    t @ _ => {
                        return Err(RayError {
                            msg: format!(
                                "expected trait type name with parameters but found `{}`",
                                t
                            ),
                            src: vec![Source {
                                span: Some(ty_span),
                                filepath: decl.src.filepath.clone(),
                            }],
                            kind: RayErrorKind::Type,
                        })
                    }
                };

                // traits should only have one type parameter
                if ty_params.len() != 1 {
                    return Err(RayError {
                        msg: format!("expected one type parameter but found {}", ty_params.len()),
                        src: vec![Source {
                            span: Some(ty_span),
                            filepath: decl.src.filepath.clone(),
                        }],
                        kind: RayErrorKind::Type,
                    });
                }

                let trait_scope = scope.append(name.clone());
                let fqn = trait_scope.to_string();
                let mut trait_ctx = ctx.clone();
                let mut ty_vars = vec![];
                for tp in ty_params.iter() {
                    if let Ty::Var(v) = tp {
                        ty_vars.push(v.clone());
                        trait_ctx.bind_var(v.to_string(), tp.clone());
                    } else {
                        return Err(RayError {
                            msg: format!("expected a type parameter but found {}", tp),
                            src: vec![Source {
                                span: Some(ty_span),
                                filepath: decl.src.filepath.clone(),
                            }],
                            kind: RayErrorKind::Type,
                        });
                    }
                }

                let trait_ty = Ty::Projection(fqn.clone(), ty_params, vec![]);

                let mut fields = vec![];
                for func in tr.funcs.iter() {
                    let func_name = match &func.name {
                        Some(n) => n.clone(),
                        _ => {
                            return Err(RayError {
                                msg: format!("trait function on `{}` does not have a name", tr.ty),
                                src: vec![Source {
                                    span: Some(func.span),
                                    filepath: decl.src.filepath.clone(),
                                }],
                                kind: RayErrorKind::Type,
                            })
                        }
                    };

                    let fn_scope = trait_scope.clone();
                    let mut fn_ctx = ctx.clone();
                    let ty = Ty::from_sig(func, &fn_scope, &decl.src.filepath, &mut fn_ctx, ctx)?;
                    let (mut q, ty) = ty.unpack_qualified_ty();
                    // add the trait type to the qualifiers
                    q.insert(0, TyPredicate::Trait(trait_ty.clone()));
                    let ty = ty
                        .qualify_with_tyvars(&q, &ty_vars.clone())
                        .quantify(ty_vars.clone());
                    ctx.bind_var(func_name.clone(), ty.clone());
                    fields.push((func_name.clone(), ty.clone()));
                    let src = Source {
                        filepath: decl.src.filepath.clone(),
                        span: Some(func.span),
                    };
                    decls.push(HirDecl::ty(func_name, ty).with_src(Some(src)));
                }

                let super_trait = tr
                    .super_trait
                    .as_ref()
                    .map(|t| Ty::from_ast_ty(&t.kind, scope, ctx));

                ctx.add_trait_ty(
                    name,
                    TraitTy {
                        path: trait_scope,
                        ty: trait_ty,
                        super_traits: super_trait.map(|s| vec![s]).unwrap_or_default(),
                        fields,
                    },
                );
            }
            DeclKind::Impl(imp) => {
                let (trait_name, ty_params) = match Ty::from_ast_ty(&imp.ty.kind, scope, ctx) {
                    Ty::Projection(name, ty_params, _) => (name, ty_params),
                    t => {
                        return Err(RayError {
                            msg: format!("`{}` is not a valid trait", t),
                            src: vec![Source {
                                span: Some(imp.ty.span.unwrap()),
                                filepath: decl.src.filepath.clone(),
                            }],
                            kind: RayErrorKind::Type,
                        })
                    }
                };

                // traits should only have one type parameter
                if ty_params.len() != 1 {
                    return Err(RayError {
                        msg: format!("expected one type argument but found {}", ty_params.len()),
                        src: vec![Source {
                            span: Some(imp.ty.span.unwrap()),
                            filepath: decl.src.filepath.clone(),
                        }],
                        kind: RayErrorKind::Type,
                    });
                }

                // lookup the trait in the context
                let trait_fqn = match ctx.lookup_fqn(&trait_name) {
                    Some(fqn) => fqn.clone(),
                    _ => {
                        return Err(RayError {
                            msg: format!("trait `{}` is not defined", trait_name),
                            src: vec![Source {
                                span: Some(imp.ty.span.unwrap()),
                                filepath: decl.src.filepath.clone(),
                            }],
                            kind: RayErrorKind::Type,
                        })
                    }
                };

                let trait_ty = match ctx.get_trait_ty(&trait_fqn) {
                    Some(t) => t.clone(),
                    _ => {
                        return Err(RayError {
                            msg: format!("trait `{}` is not defined", trait_name),
                            src: vec![Source {
                                span: Some(imp.ty.span.unwrap()),
                                filepath: decl.src.filepath.clone(),
                            }],
                            kind: RayErrorKind::Type,
                        })
                    }
                };

                // get the type parameter of the original trait
                let ty_param = match trait_ty.ty.get_ty_params()[0] {
                    Ty::Var(v) => v.clone(),
                    _ => {
                        return Err(RayError {
                            msg: str!("expected a type parameter for trait"),
                            src: vec![Source {
                                span: Some(imp.ty.span.unwrap()),
                                filepath: decl.src.filepath.clone(),
                            }],
                            kind: RayErrorKind::Type,
                        })
                    }
                };

                let base_ty = ty_params[0].clone();
                let impl_scope = scope.append(&base_ty);
                let mut impl_ctx = ctx.clone();
                if !is_extern {
                    let mut impl_set = HashSet::new();
                    if let Some(funcs) = &imp.funcs {
                        for func in funcs {
                            let func_name = if let ExprKind::Fn(f) = &func.kind {
                                match &f.sig.name {
                                    Some(n) => n.clone(),
                                    _ => {
                                        return Err(RayError {
                                            msg: format!(
                                                "trait function on `{}` does not have a name",
                                                trait_name
                                            ),
                                            src: vec![Source {
                                                span: Some(f.sig.span),
                                                filepath: decl.src.filepath.clone(),
                                            }],
                                            kind: RayErrorKind::Type,
                                        })
                                    }
                                }
                            } else {
                                unreachable!()
                            };

                            let mut func = func.clone();
                            if let ExprKind::Fn(f) = &mut func.kind {
                                // make this a fully-qualified name
                                let fqn = impl_scope.append(&func_name).to_string();
                                f.sig.name = Some(fqn)
                            }

                            impl_set.insert(func_name);
                            deferred_funcs.push(func);
                        }
                    }

                    if let Some(ext) = &imp.externs {
                        for e in ext {
                            let name = e.get_name().unwrap();
                            let fqn = impl_scope.append(&name).to_string();
                            impl_set.insert(name);
                            let mut e = e.clone();
                            if let DeclKind::Extern(d) = &mut e.kind {
                                if let DeclKind::Fn(sig) = &mut d.kind {
                                    sig.name = Some(fqn);
                                }
                            }

                            let (d, f) = HirModule::convert_decl(scope, &e, true, &mut impl_ctx)?;
                            decls.extend(d);
                            deferred_funcs.extend(f);
                        }
                    }

                    // make sure that everything has been implemented
                    for (n, _) in trait_ty.fields.iter() {
                        if !impl_set.contains(n) {
                            return Err(RayError {
                                msg: format!("trait implementation is missing for field `{}`", n),
                                src: vec![Source {
                                    span: Some(imp.ty.span.unwrap()),
                                    filepath: decl.src.filepath.clone(),
                                }],
                                kind: RayErrorKind::Type,
                            });
                        }
                    }

                    // TODO: consts
                }

                // create a subst mapping the type parameter to the argument
                let sub = subst! { ty_param => base_ty.clone() };
                let trait_ty = trait_ty.ty.clone().apply_subst(&sub);

                let mut predicates = vec![];
                for q in imp.qualifiers.iter() {
                    predicates.push(TyPredicate::from_ast_ty(
                        &q,
                        &impl_scope,
                        &decl.src.filepath,
                        &mut impl_ctx,
                    )?);
                }

                let impl_ty = ImplTy {
                    trait_ty,
                    base_ty,
                    predicates,
                };
                ctx.add_impl(trait_fqn, impl_ty);
            }
            _ => unimplemented!("decl to type: {}", decl),
        };

        Ok((decls, deferred_funcs))
    }
}

pub trait IntoHirNode
where
    Self: Sized,
{
    #[inline(always)]
    fn to_hir_node(self, scope: &Path, filepath: &FilePath, ctx: &mut Ctx) -> RayResult<HirNode> {
        let mut deq = VecDeque::new();
        self.to_hir_node_with(&mut deq, scope, filepath, ctx)
    }

    fn to_hir_node_with(
        self,
        rest: &mut VecDeque<Expr>,
        scope: &Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode>;
}

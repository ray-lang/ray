use std::collections::HashSet;

use crate::{
    ast::{Decl, Expr, HasSource, Modifier, Node, Path, SourceInfo},
    errors::{RayError, RayErrorKind, RayResult},
    span::Source,
    subst,
    typing::{
        predicate::TyPredicate,
        traits::HasType,
        ty::{ImplTy, StructTy, TraitTy, Ty},
        ApplySubst, TyCtx,
    },
};

use super::{get_ty_vars, HirDecl, IntoHirDecl, IntoHirNode, Param};

impl<'a> IntoHirDecl<SourceInfo> for &'a Node<Decl<SourceInfo>, SourceInfo> {
    type Output = Vec<Node<HirDecl<SourceInfo>, SourceInfo>>;

    fn to_hir_decl(self, is_extern: bool, ctx: &mut TyCtx) -> RayResult<Self::Output> {
        let id = self.id;
        let info = self.info.clone();
        let scope = &info.path;
        let mut decls = vec![];
        match &self.value {
            Decl::Extern(decl) => return decl.to_hir_decl(true, ctx),
            Decl::Mutable(n) | Decl::Name(n) => {
                let name = n.name.clone();
                let ty = n.ty.as_ref().unwrap().clone_value().from_ast_ty(scope, ctx);
                ctx.bind_var(name.clone(), ty.clone());
                decls.push(Node {
                    id,
                    info,
                    value: HirDecl::Extern(
                        Path::from(name),
                        ty,
                        matches!(self.value, Decl::Mutable(_)),
                        None,
                    ),
                });
            }
            Decl::Struct(st) => {
                let name = st.name.to_string();
                let struct_path = if Ty::is_builtin(&name) {
                    Path::from(name.clone())
                } else {
                    scope.clone()
                };
                let fqn = struct_path.to_string();

                let mut struct_ctx = ctx.clone();
                let ty_vars = get_ty_vars(
                    st.ty_params.as_ref(),
                    &struct_path,
                    &self.src().filepath,
                    &mut struct_ctx,
                )?;

                let mut fields_vec = vec![];
                let mut field_tys = vec![];
                if let Some(fields) = &st.fields {
                    for field in fields.iter() {
                        let ty = if let Some(ty) = &field.ty {
                            ty.clone_value().from_ast_ty(&struct_path, &mut struct_ctx)
                        } else {
                            return Err(RayError {
                                msg: format!("struct field on `{}` does not have a type", st.name),
                                src: vec![Source {
                                    span: Some(field.span),
                                    filepath: self.src().filepath.clone(),
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
            }
            Decl::FnSig(sig) => {
                let name = sig
                    .name
                    .as_ref()
                    .ok_or_else(|| RayError {
                        msg: format!("externed function must have a name"),
                        src: vec![self.src().clone()],
                        kind: RayErrorKind::Type,
                    })?
                    .clone();

                let mut fn_ctx = ctx.clone();
                let func_fqn = Path::from(name);

                // make sure that the signature is fully typed
                let ty = Ty::from_sig(sig, scope, &self.src().filepath, &mut fn_ctx, ctx)?;
                let src = if sig.modifiers.contains(&Modifier::Wasi) {
                    Some(str!("wasi_snapshot_preview1"))
                } else {
                    None
                };

                decls.push(Node {
                    id,
                    info,
                    value: HirDecl::Extern(func_fqn, ty, false, src),
                });
            }
            Decl::Fn(func) => {
                let name = func
                    .sig
                    .name
                    .as_ref()
                    .ok_or_else(|| RayError {
                        msg: format!("top-level function must have a name"),
                        src: vec![self.src().clone()],
                        kind: RayErrorKind::Type,
                    })?
                    .clone();

                let mut func_fqn = Path::from(name.clone());
                if func_fqn.len() == 1 {
                    func_fqn = scope.clone();
                }

                ctx.add_fqn(name.clone(), func_fqn.clone());

                let mut fn_ctx = ctx.clone();
                let mut params = vec![];
                for p in func.sig.params.iter() {
                    let n = match p.name() {
                        Some(n) => n.clone(),
                        _ => {
                            return Err(RayError {
                                msg: str!("parameter has no name"),
                                src: vec![Source {
                                    span: Some(p.span()),
                                    filepath: info.src.filepath.clone(),
                                }],
                                kind: RayErrorKind::Type,
                            })
                        }
                    };

                    params.push(Param::new(
                        n,
                        p.ty()
                            .map(|t| t.clone().from_ast_ty(&func_fqn, &mut fn_ctx)),
                    ));
                }

                let param_tys = params
                    .iter()
                    .map(|p| p.get_ty().cloned())
                    .collect::<Vec<_>>();

                let num_typed = param_tys
                    .iter()
                    .fold(0, |acc, p| if p.is_some() { acc + 1 } else { acc });

                if num_typed != 0 && num_typed != param_tys.len() {
                    panic!("cannot infer type of only some parameters");
                }

                if num_typed == param_tys.len() {
                    let ty =
                        Ty::from_sig(&func.sig, &func_fqn, &info.src.filepath, &mut fn_ctx, ctx)?;
                    decls.push(Node::new(
                        HirDecl::Type(func_fqn.clone(), ty, false, None),
                        info.clone(),
                    ));
                }

                let body = func.body.clone().unwrap();
                let body_id = body.id;
                let body_info = body.info.clone();
                let fn_body = body.to_hir_node(&func_fqn, body_id, &body_info, ctx)?;

                decls.push(Node {
                    id,
                    info,
                    value: HirDecl::Fn(
                        func_fqn,
                        params,
                        Box::new(fn_body),
                        func.sig.decorators.clone(),
                    ),
                });
            }
            Decl::Trait(tr) => {
                let ty_span = *tr.ty.span().unwrap();
                let parent_scope = scope.parent();
                let (name, ty_params) = match tr.ty.clone_value().from_ast_ty(scope, ctx) {
                    Ty::Projection(n, tp, _) => (n, tp),
                    t @ _ => {
                        return Err(RayError {
                            msg: format!(
                                "expected trait type name with parameters but found `{}`",
                                t
                            ),
                            src: vec![Source {
                                span: Some(ty_span),
                                filepath: self.src().filepath.clone(),
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
                            filepath: self.src().filepath.clone(),
                        }],
                        kind: RayErrorKind::Type,
                    });
                }

                let fqn = scope.to_string();
                let mut trait_ctx = ctx.clone();
                let mut ty_vars = vec![];
                let tp = &ty_params[0];
                if let Ty::Var(v) = tp {
                    ty_vars.push(v.clone());
                    trait_ctx.bind_var(v.to_string(), tp.clone());
                } else {
                    return Err(RayError {
                        msg: format!("expected a type parameter but found {}", tp),
                        src: vec![Source {
                            span: Some(ty_span),
                            filepath: self.src().filepath.clone(),
                        }],
                        kind: RayErrorKind::Type,
                    });
                }

                let base_ty = tp.clone();
                let base_ty_fqn = base_ty.get_path().unwrap();
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
                                    filepath: self.src().filepath.clone(),
                                }],
                                kind: RayErrorKind::Type,
                            })
                        }
                    };

                    let mut fn_ctx = ctx.clone();
                    let ty = Ty::from_sig(func, scope, &self.src().filepath, &mut fn_ctx, ctx)?;
                    let (mut q, ty) = ty.unpack_qualified_ty();
                    // add the trait type to the qualifiers
                    q.insert(0, TyPredicate::Trait(trait_ty.clone()));
                    let ty = ty.qualify(&q, &ty_vars.clone()).quantify(ty_vars.clone());

                    let func_fqn = base_ty_fqn.append(&func_name);
                    ctx.add_fqn(func_name.clone(), func_fqn.clone());
                    ctx.bind_var(func_fqn.to_string(), ty.clone());

                    fields.push((func_name.clone(), ty.clone()));
                    let mut info = info.clone();
                    info.set_src(Source {
                        filepath: self.src().filepath.clone(),
                        span: Some(func.span),
                    });

                    decls.push(Node {
                        id,
                        info,
                        value: HirDecl::member(func_fqn, ty),
                    });
                }

                let super_trait = tr
                    .super_trait
                    .clone()
                    .map(|t| t.take_value().from_ast_ty(&parent_scope, ctx));

                ctx.add_trait_ty(
                    name,
                    TraitTy {
                        path: scope.clone(),
                        ty: trait_ty,
                        super_traits: super_trait.map(|s| vec![s]).unwrap_or_default(),
                        fields,
                    },
                );
            }
            Decl::Impl(imp) => {
                let parent_scope = scope.parent();
                let (trait_name, ty_params) =
                    match imp.ty.clone_value().from_ast_ty(&parent_scope, ctx) {
                        Ty::Projection(name, ty_params, _) => (name, ty_params),
                        t => {
                            return Err(RayError {
                                msg: format!("`{}` is not a valid trait", t),
                                src: vec![Source {
                                    span: Some(*imp.ty.span().unwrap()),
                                    filepath: self.src().filepath.clone(),
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
                            span: Some(*imp.ty.span().unwrap()),
                            filepath: self.src().filepath.clone(),
                        }],
                        kind: RayErrorKind::Type,
                    });
                }

                // lookup the trait in the context
                let trait_fqn = Path::from(trait_name.as_str());
                let trait_ty = match ctx.get_trait_ty(&trait_fqn) {
                    Some(t) => t.clone(),
                    _ => {
                        return Err(RayError {
                            msg: format!("trait `{}` is not defined", trait_fqn),
                            src: vec![Source {
                                span: Some(*imp.ty.span().unwrap()),
                                filepath: self.src().filepath.clone(),
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
                                span: Some(*imp.ty.span().unwrap()),
                                filepath: self.src().filepath.clone(),
                            }],
                            kind: RayErrorKind::Type,
                        })
                    }
                };

                let base_ty = ty_params[0].clone();
                let impl_scope = base_ty.get_path().unwrap();
                let mut impl_ctx = ctx.clone();
                if !is_extern {
                    let mut impl_set = HashSet::new();
                    if let Some(funcs) = &imp.funcs {
                        for func in funcs {
                            let func_name = if let Decl::Fn(f) = &func.value {
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
                                                filepath: self.src().filepath.clone(),
                                            }],
                                            kind: RayErrorKind::Type,
                                        })
                                    }
                                }
                            } else {
                                unreachable!()
                            };

                            let mut func = func.clone();
                            if let Decl::Fn(f) = &mut func.value {
                                // make this a fully-qualified name
                                let fqn = impl_scope.append(&func_name).to_string();
                                f.sig.name = Some(fqn);
                            }

                            impl_set.insert(func_name);
                            decls.extend(func.to_hir_decl(false, &mut impl_ctx)?);
                        }
                    }

                    if let Some(ext) = &imp.externs {
                        for e in ext {
                            let name = e.get_name().unwrap();
                            impl_set.insert(name);
                            decls.extend(e.to_hir_decl(true, &mut impl_ctx)?);
                        }
                    }

                    // make sure that everything has been implemented
                    for (n, _) in trait_ty.fields.iter() {
                        if !impl_set.contains(n) {
                            return Err(RayError {
                                msg: format!("trait implementation is missing for field `{}`", n),
                                src: vec![Source {
                                    span: Some(*imp.ty.span().unwrap()),
                                    filepath: self.src().filepath.clone(),
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
                        &self.src().filepath,
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
            _ => unimplemented!("decl to type: {}", self),
        };

        Ok(decls)
    }
}

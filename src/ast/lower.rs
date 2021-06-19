use std::{
    collections::{HashMap, HashSet},
    ops::{Deref, DerefMut},
};

use ast::{
    token::{Token, TokenKind},
    Call, Impl,
};

use crate::{
    ast,
    errors::{RayError, RayErrorKind, RayResult},
    pathlib::FilePath,
    span::{parsed::Parsed, Source, SourceMap, Span},
    subst,
    typing::{
        predicate::TyPredicate,
        ty::{ImplTy, StructTy, TraitTy, Ty, TyVar},
        ApplySubst, TyCtx,
    },
    utils::try_replace,
};

use super::{Decl, Expr, Extern, Fn, Modifier, Node, Path, Struct, Trait, TypeParams};

fn get_ty_vars(
    ty_params: Option<&TypeParams>,
    scope: &Path,
    filepath: &FilePath,
    src_module: &Path,
    tcx: &mut TyCtx,
) -> Result<Vec<TyVar>, RayError> {
    let mut ty_vars = vec![];
    if let Some(ty_params) = ty_params {
        for tp in ty_params.tys.iter() {
            let mut ty = tp.clone_value();
            ty.resolve_ty(scope, tcx);
            if let Ty::Var(v) = ty {
                ty_vars.push(v.clone());
            } else {
                return Err(RayError {
                    msg: format!("expected type parameter, but found `{}`", tp),
                    src: vec![Source::new(
                        filepath.clone(),
                        tp.span().copied().unwrap(),
                        Path::new(),
                        src_module.clone(),
                    )],
                    kind: RayErrorKind::Type,
                });
            }
        }
    }

    Ok(ty_vars)
}

struct Sourced<'a, T>(pub &'a mut T, pub &'a Source);

impl<'a, T> Deref for Sourced<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a, T> DerefMut for Sourced<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a, T> Sourced<'a, T> {
    pub fn unpack_mut(&mut self) -> (&mut T, &Source) {
        (self.0, self.1)
    }

    pub fn value(&self) -> &T {
        &self.0
    }

    pub fn src_module(&self) -> &Path {
        &self.1.src_module
    }
}

pub trait LowerAST
where
    Self: Sized,
{
    type Output;

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output>;
}

impl<T, U> LowerAST for Box<T>
where
    T: LowerAST<Output = U>,
{
    type Output = U;

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<U> {
        self.as_mut().lower(srcmap, scope_map, tcx)
    }
}

impl<T, U> LowerAST for Option<T>
where
    T: LowerAST<Output = U>,
{
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<()> {
        if let Some(v) = self {
            v.lower(srcmap, scope_map, tcx)?;
        }
        Ok(())
    }
}

impl<T, U> LowerAST for Vec<T>
where
    T: LowerAST<Output = U>,
{
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<()> {
        for t in self.iter_mut() {
            t.lower(srcmap, scope_map, tcx)?;
        }
        Ok(())
    }
}

impl LowerAST for Node<Decl> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<()> {
        let src = srcmap.get(self);
        let scope = &src.path;
        let decl = &mut self.value;
        match decl {
            Decl::Extern(decl) => {
                Sourced(decl, &src).lower(srcmap, scope_map, tcx)?;
            }
            Decl::Mutable(n) | Decl::Name(n) => {
                if let Some(ty) = n.value.ty.as_deref_mut() {
                    ty.resolve_ty(scope, tcx);
                }
                let ty = n.ty.as_deref().unwrap().clone();
                tcx.bind_var(&n.path, ty);
            }
            d @ Decl::Declare(_) => unimplemented!("decl to type: {}", d),
            Decl::Fn(func) => Sourced(func, &src).lower(srcmap, scope_map, tcx)?,
            Decl::FnSig(sig) => todo!("lower: Decl::FnSig: {:?}", sig),
            Decl::Struct(st) => Sourced(st, &src).lower(srcmap, scope_map, tcx)?,
            Decl::Trait(tr) => Sourced(tr, &src).lower(srcmap, scope_map, tcx)?,
            Decl::TypeAlias(name, ty) => todo!("lower: Decl::TypeAlias: {:?} = {:?}", name, ty),
            Decl::Impl(im) => Sourced(im, &src).lower(srcmap, scope_map, tcx)?,
        };
        Ok(())
    }
}

impl LowerAST for Sourced<'_, Extern> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        _: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<()> {
        let (ext, src) = self.unpack_mut();
        match ext.decl_mut() {
            Decl::Mutable(_) => todo!(),
            Decl::Name(_) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::FnSig(sig) => {
                let name = sig
                    .name
                    .as_ref()
                    .ok_or_else(|| RayError {
                        msg: format!("externed function must have a name"),
                        src: vec![src.clone()],
                        kind: RayErrorKind::Type,
                    })?
                    .clone();
                sig.path = Path::from(name);

                // make sure that the signature is fully typed
                let mut fn_ctx = tcx.clone();
                let ty = Ty::from_sig(sig, &src.path, &src.filepath, &mut fn_ctx, tcx, srcmap)?;
                sig.ty = Some(ty);

                if sig.modifiers.contains(&Modifier::Wasi) {
                    *self.src_mut() = Some(str!("wasi_snapshot_preview1"));
                }
            }
            _ => unreachable!(),
        }

        Ok(())
    }
}

impl LowerAST for Sourced<'_, Struct> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        _: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<()> {
        let (st, src) = self.unpack_mut();
        let name = st.name.to_string();
        let struct_path = if Ty::is_builtin(&name) {
            Path::from(name.clone())
        } else {
            src.path.clone()
        };

        let mut struct_tcx = tcx.clone();
        let ty_vars = get_ty_vars(
            st.ty_params.as_ref(),
            &struct_path,
            &src.filepath,
            &src.src_module,
            &mut struct_tcx,
        )?;

        let mut fields_vec = vec![];
        let mut field_tys = vec![];
        if let Some(fields) = &st.fields {
            for field in fields.iter() {
                let ty = if let Some(ty) = &field.ty {
                    let mut ty = ty.clone_value();
                    ty.resolve_ty(&struct_path, &mut struct_tcx);
                    ty
                } else {
                    let src = srcmap.get(field);
                    return Err(RayError {
                        msg: format!("struct field on `{}` does not have a type", st.name),
                        src: vec![src],
                        kind: RayErrorKind::Type,
                    });
                };

                fields_vec.push((field.path.to_string(), ty.clone()));
                field_tys.push(ty);
            }
        }

        let struct_ty = Ty::Projection(
            struct_path.to_string(),
            ty_vars.iter().map(|t| Ty::Var(t.clone())).collect(),
        );
        tcx.add_struct_ty(
            name,
            StructTy {
                path: struct_path,
                ty: struct_ty.clone(),
                fields: fields_vec,
            },
        );
        Ok(())
    }
}

impl LowerAST for Sourced<'_, Trait> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        _: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        let (tr, src) = self.unpack_mut();
        let scope = &src.path;
        let ty_span = *tr.ty.span().unwrap();
        let parent_scope = scope.parent();
        tr.ty.resolve_ty(scope, tcx);

        let (name, ty_params) = match tr.ty.deref() {
            Ty::Projection(n, tp) => (n.clone(), tp.clone()),
            t @ _ => {
                return Err(RayError {
                    msg: format!("expected trait type name with parameters but found `{}`", t),
                    src: vec![src.respan(ty_span)],
                    kind: RayErrorKind::Type,
                })
            }
        };

        // traits should only have one type parameter
        if ty_params.len() != 1 {
            return Err(RayError {
                msg: format!("expected one type parameter but found {}", ty_params.len()),
                src: vec![src.respan(ty_span)],
                kind: RayErrorKind::Type,
            });
        }

        let fqn = scope.to_string();
        let mut trait_ctx = tcx.clone();
        let mut ty_vars = vec![];
        let tp = &ty_params[0];
        if let Ty::Var(v) = tp {
            ty_vars.push(v.clone());
            trait_ctx.bind_var(v.to_string(), tp.clone());
        } else {
            return Err(RayError {
                msg: format!("expected a type parameter but found {}", tp),
                src: vec![src.respan(ty_span)],
                kind: RayErrorKind::Type,
            });
        }

        let base_ty = tp.clone();
        let base_ty_fqn = base_ty.get_path().unwrap();
        log::debug!("base_ty_fqn = {}", base_ty_fqn);
        let trait_ty = Ty::Projection(fqn.clone(), ty_params);

        let mut fields = vec![];
        for func in tr.funcs.iter_mut() {
            let func_name = match &func.name {
                Some(n) => n.clone(),
                _ => {
                    return Err(RayError {
                        msg: format!("trait function on `{}` does not have a name", tr.ty),
                        src: vec![src.respan(func.span)],
                        kind: RayErrorKind::Type,
                    })
                }
            };

            let mut fn_ctx = tcx.clone();
            let ty = Ty::from_sig(func, scope, &src.filepath, &mut fn_ctx, tcx, srcmap)?;
            let (mut q, ty) = ty.unpack_qualified_ty();
            // add the trait type to the qualifiers
            q.insert(0, TyPredicate::Trait(trait_ty.clone()));
            let ty = ty.qualify(&q, &ty_vars.clone()).quantify(ty_vars.clone());

            let func_fqn = base_ty_fqn.append(&func_name);
            log::debug!("add fqn: {} => {}", func_name, func_fqn);
            tcx.add_fqn(func_name.clone(), func_fqn.clone());
            tcx.bind_var(func_fqn.to_string(), ty.clone());

            fields.push((func_name.clone(), ty.clone()));

            func.path = func_fqn;
            func.ty = Some(ty);
        }

        let super_trait = tr.super_trait.clone().map(|ty| {
            let mut ty = ty.take_value();
            ty.resolve_ty(&parent_scope, tcx);
            ty
        });

        tcx.add_trait_ty(
            name,
            TraitTy {
                path: scope.clone(),
                ty: trait_ty,
                super_traits: super_trait.map(|s| vec![s]).unwrap_or_default(),
                fields,
            },
        );

        Ok(())
    }
}

impl LowerAST for Sourced<'_, Impl> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        let (imp, src) = self.unpack_mut();
        let scope = &src.path;
        imp.ty.resolve_ty(scope, tcx);

        let (trait_name, ty_params) = match imp.ty.deref() {
            Ty::Projection(name, ty_params) => (name.clone(), ty_params.clone()),
            t => {
                return Err(RayError {
                    msg: format!("`{}` is not a valid trait", t),
                    src: vec![src.respan(*imp.ty.span().unwrap())],
                    kind: RayErrorKind::Type,
                })
            }
        };

        // traits should only have one type parameter
        if ty_params.len() != 1 {
            return Err(RayError {
                msg: format!("expected one type argument but found {}", ty_params.len()),
                src: vec![src.respan(*imp.ty.span().unwrap())],
                kind: RayErrorKind::Type,
            });
        }

        // lookup the trait in the context
        let trait_fqn = Path::from(trait_name.as_str());
        log::debug!("found fqn: {}", trait_fqn);
        let trait_ty = match tcx.get_trait_ty(&trait_fqn) {
            Some(t) => t.clone(),
            _ => {
                return Err(RayError {
                    msg: format!("trait `{}` is not defined", trait_fqn),
                    src: vec![src.respan(*imp.ty.span().unwrap())],
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
                    src: vec![src.respan(*imp.ty.span().unwrap())],
                    kind: RayErrorKind::Type,
                })
            }
        };

        let base_ty = ty_params[0].clone();
        let impl_scope = base_ty.get_path().unwrap();
        let mut impl_ctx = tcx.clone();
        let mut impl_set = HashSet::new();
        if let Some(funcs) = &mut imp.funcs {
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
                                src: vec![src.respan(f.sig.span)],
                                kind: RayErrorKind::Type,
                            })
                        }
                    }
                } else {
                    unreachable!()
                };

                if let Decl::Fn(f) = &mut func.value {
                    // make this a fully-qualified name
                    f.sig.path = impl_scope.append(&func_name);
                }

                impl_set.insert(func_name);
                func.lower(srcmap, scope_map, tcx)?;
            }
        }

        if let Some(ext) = &mut imp.externs {
            for e in ext {
                let name = e.get_name().unwrap();
                impl_set.insert(name);
                e.lower(srcmap, scope_map, tcx)?;
            }
        }

        // make sure that everything has been implemented
        for (n, _) in trait_ty.fields.iter() {
            if !impl_set.contains(n) {
                return Err(RayError {
                    msg: format!("trait implementation is missing for field `{}`", n),
                    src: vec![src.respan(*imp.ty.span().unwrap())],
                    kind: RayErrorKind::Type,
                });
            }
        }

        // TODO: consts

        // create a subst mapping the type parameter to the argument
        let sub = subst! { ty_param => base_ty.clone() };
        let trait_ty = trait_ty.ty.clone().apply_subst(&sub);

        let mut predicates = vec![];
        for q in imp.qualifiers.iter() {
            predicates.push(TyPredicate::from_ast_ty(
                &q,
                &impl_scope,
                &src.filepath,
                &mut impl_ctx,
            )?);
        }

        let impl_ty = ImplTy {
            trait_ty,
            base_ty,
            predicates,
        };
        tcx.add_impl(trait_fqn, impl_ty);
        Ok(())
    }
}

impl LowerAST for Sourced<'_, Fn> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<()> {
        let (func, src) = self.unpack_mut();
        let name = func
            .sig
            .name
            .as_ref()
            .ok_or_else(|| RayError {
                msg: format!("top-level function must have a name"),
                src: vec![src.clone()],
                kind: RayErrorKind::Type,
            })?
            .clone();

        let func_fqn = if !func.sig.is_method {
            let fqn = src.path.append(name.clone());
            log::debug!("add fqn: {} => {}", name, fqn);
            tcx.add_fqn(name, fqn.clone());
            tcx.nametree_mut().add_full_name(&fqn.to_vec());
            fqn
        } else {
            func.sig.path.clone()
        };

        let mut fn_tcx = tcx.clone();
        let mut num_typed = 0;
        for p in func.sig.params.iter_mut() {
            if p.name().is_none() {
                let src = srcmap.get(p);
                return Err(RayError {
                    msg: str!("parameter has no name"),
                    src: vec![src],
                    kind: RayErrorKind::Type,
                });
            }

            if p.ty().is_some() {
                num_typed += 1;
            }
        }

        if num_typed != 0 && num_typed != func.sig.params.len() {
            panic!("cannot infer type of only some parameters");
        }

        if num_typed == func.sig.params.len() {
            func.sig.ty = Some(Ty::from_sig(
                &func.sig,
                &func_fqn,
                &src.filepath,
                &mut fn_tcx,
                tcx,
                srcmap,
            )?);
        }

        func.body.lower(srcmap, scope_map, &mut fn_tcx)?;

        Ok(())
    }
}

impl LowerAST for Node<Expr> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<()> {
        let src = srcmap.get(self);
        let new_value = match &mut self.value {
            Expr::Assign(assign) => return assign.lower(srcmap, scope_map, tcx),
            Expr::Asm(asm) => return Sourced(asm, &src).lower(srcmap, scope_map, tcx),
            Expr::BinOp(b) => {
                let call = Sourced(b, &src).lower(srcmap, scope_map, tcx)?;
                Expr::Call(call)
            }
            Expr::Block(b) => return b.lower(srcmap, scope_map, tcx),
            Expr::Break(value) => {
                if let Some(value) = value {
                    value.lower(srcmap, scope_map, tcx)?;
                }
                return Ok(());
            }
            Expr::Call(c) => return c.lower(srcmap, scope_map, tcx),
            Expr::Cast(c) => return Sourced(c, &src).lower(srcmap, scope_map, tcx),
            Expr::Closure(_) => todo!("lower: Expr::Closure: {:?}", self),
            Expr::Curly(c) => return Sourced(c, &src).lower(srcmap, scope_map, tcx),
            Expr::DefaultValue(_) => todo!("lower: Expr::DefaultValue: {:?}", self),
            Expr::Dot(d) => return d.lower(srcmap, scope_map, tcx),
            Expr::Fn(_) => todo!("lower: Expr::Fn: {:?}", self),
            Expr::For(_) => todo!("lower: Expr::For: {:?}", self),
            Expr::If(if_ex) => return Sourced(if_ex, &src).lower(srcmap, scope_map, tcx),
            Expr::Index(_) => todo!("lower: Expr::Index: {:?}", self),
            Expr::Labeled(_, _) => todo!("lower: Expr::Labeled: {:?}", self),
            Expr::List(l) => return l.lower(srcmap, scope_map, tcx),
            Expr::Literal(_) => return Ok(()),
            Expr::Loop(loop_stmt) => return Ok(()),
            Expr::Name(n) => return Sourced(n, &src).lower(srcmap, scope_map, tcx),
            Expr::Pattern(p) => return Sourced(p, &src).lower(srcmap, scope_map, tcx),
            Expr::Path(_) => return Ok(()),
            Expr::Paren(ex) => return ex.lower(srcmap, scope_map, tcx),
            Expr::Range(r) => return r.lower(srcmap, scope_map, tcx),
            Expr::Return(_) => todo!("lower: Expr::Return: {:?}", self),
            Expr::Sequence(seq) => return seq.lower(srcmap, scope_map, tcx),
            Expr::Tuple(t) => return t.lower(srcmap, scope_map, tcx),
            Expr::Type(_) => todo!("lower: Expr::Type: {:?}", self),
            Expr::TypeAnnotated(ex, ty) => {
                ty.resolve_ty(&src.path, tcx);
                return ex.lower(srcmap, scope_map, tcx);
            }
            Expr::UnaryOp(u) => {
                let call = Sourced(u, &src).lower(srcmap, scope_map, tcx)?;
                Expr::Call(call)
            }
            Expr::Unsafe(_) => todo!("lower: Expr::Unsafe: {:?}", self),
            Expr::While(w) => return Sourced(w, &src).lower(srcmap, scope_map, tcx),
        };

        let _ = std::mem::replace(&mut self.value, new_value);
        Ok(())
    }
}

fn convert_binop(
    op: &ast::InfixOp,
    op_span: Span,
    lhs: Node<Expr>,
    rhs: Node<Expr>,
    srcmap: &mut SourceMap,
) -> RayResult<Call> {
    let lhs_src = srcmap.get(&lhs);
    let name = op.to_string();
    let op_var = Node::new(ast::Name::new(name));
    srcmap.set_src(&op_var, lhs_src.respan(op_span));

    let lhs_span = lhs_src.span.unwrap();
    let lhs = Node::new(Expr::Dot(ast::Dot {
        lhs: Box::new(lhs),
        rhs: op_var,
        dot: Token {
            kind: TokenKind::Dot,
            span: op_span,
        },
    }));

    srcmap.set_src(&lhs, lhs_src.respan(lhs_span.extend_to(&op_span)));

    Ok(Call::new(lhs, vec![rhs]))
}

impl LowerAST for ast::Assign {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<()> {
        if let ast::InfixOp::AssignOp(op) = self.op.clone() {
            let lhs_src = srcmap.get(&self.lhs);
            let lhs = self.lhs.clone().try_take_map(|pat| match pat {
                ast::Pattern::Name(n) => Ok(Expr::Name(n)),
                ast::Pattern::Sequence(_) | ast::Pattern::Tuple(_) | ast::Pattern::Deref(_) => {
                    Err(RayError {
                        msg: str!("cannot use expression as l-value for re-assignment"),
                        src: vec![lhs_src],
                        kind: RayErrorKind::Type,
                    })
                }
            })?;

            let op_span = self.op_span;
            try_replace::<_, _, RayError>(&mut self.rhs, |mut rhs| {
                rhs.lower(srcmap, scope_map, tcx)?;

                let lhs_src = srcmap.get(&lhs);
                let rhs_src = srcmap.get(&rhs);
                let src = lhs_src.extend_to(&rhs_src);
                let call = convert_binop(&op, op_span, lhs, *rhs, srcmap)?;
                let node = Node::new(Expr::Call(call));
                srcmap.set_src(&node, src);
                Ok(Box::new(node))
            })?;
        } else {
            self.rhs.lower(srcmap, scope_map, tcx)?;
        };

        if matches!(self.op, ast::InfixOp::AssignOp(_)) {
            self.op = ast::InfixOp::Assign;
        }

        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::asm::Asm> {
    type Output = ();

    fn lower(
        &mut self,
        _: &mut SourceMap,
        _: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<()> {
        let (asm, info) = self.unpack_mut();
        let scope = &info.path;
        asm.ret_ty.as_deref_mut().map(|t| t.resolve_ty(scope, tcx));
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::BinOp> {
    type Output = ast::Call;

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        let (binop, _) = self.unpack_mut();
        let mut lhs = binop.lhs.as_ref().clone();
        lhs.lower(srcmap, scope_map, tcx)?;
        let mut rhs = binop.rhs.as_ref().clone();
        rhs.lower(srcmap, scope_map, tcx)?;

        convert_binop(&binop.op, binop.op_span, lhs, rhs, srcmap)
    }
}

impl LowerAST for ast::Block {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        self.stmts.lower(srcmap, scope_map, tcx)
    }
}

impl LowerAST for ast::Call {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        self.lhs.lower(srcmap, scope_map, tcx)?;
        self.args.items.lower(srcmap, scope_map, tcx)
    }
}

impl LowerAST for Sourced<'_, ast::Cast> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        let (cast, info) = self.unpack_mut();
        cast.lhs.lower(srcmap, scope_map, tcx)?;
        cast.ty.resolve_ty(&info.path, tcx);
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::Curly> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        _: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        if self.lhs.is_none() {
            unimplemented!("anon struct construction: {}", self.value())
        }

        let (curly, src) = self.unpack_mut();
        let (lhs, lhs_src) = curly.lhs.as_ref().unwrap().clone().take();
        let lhs_span = lhs_src.span.unwrap();
        let struct_fqn = match tcx.lookup_fqn(&lhs.name().unwrap()) {
            Some(fqn) => fqn.clone(),
            _ => {
                return Err(RayError {
                    msg: format!("struct type `{}` is undefined", lhs),
                    src: vec![src.respan(lhs_span)],
                    kind: RayErrorKind::Type,
                })
            }
        };

        curly.lhs = Some(Parsed::new(struct_fqn.clone(), lhs_src));

        let struct_ty = match tcx.get_struct_ty(&struct_fqn) {
            Some(t) => t,
            _ => {
                return Err(RayError {
                    msg: format!("struct type `{}` is undefined", lhs),
                    src: vec![src.respan(lhs_span)],
                    kind: RayErrorKind::Type,
                })
            }
        };

        curly.ty = struct_ty.ty.clone();
        let mut idx = HashMap::new();
        for (i, (f, _)) in struct_ty.fields.iter().enumerate() {
            idx.insert(f.clone(), i);
        }

        let mut param_map = vec![];
        for el in curly.elements.drain(..) {
            let el_span = srcmap.span_of(&el);
            let (n, name_span, el) = match el.value {
                ast::CurlyElement::Name(n) => {
                    (n.clone(), el_span, Node::with_id(el.id, Expr::Name(n)))
                }
                ast::CurlyElement::Labeled(n, ex) => (n, el_span, ex),
            };

            let field_str = n.to_string();
            if let Some(i) = idx.get(&field_str) {
                param_map.push((*i, n.clone(), el));
            } else {
                return Err(RayError {
                    msg: format!("struct `{}` does not have field `{}`", lhs, n),
                    src: vec![src.respan(name_span)],
                    kind: RayErrorKind::Type,
                });
            }
        }

        param_map.sort_by_key(|(i, ..)| *i);

        let mut elements = vec![];
        for (_, n, el) in param_map.into_iter() {
            let src = srcmap.get(&el);
            let node = Node::new(ast::CurlyElement::Labeled(n, el));
            srcmap.set_src(&node, src);
            elements.push(node);
        }

        curly.elements = elements;
        Ok(())
    }
}

impl LowerAST for ast::Dot {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        self.lhs.lower(srcmap, scope_map, tcx)
    }
}

impl LowerAST for Sourced<'_, ast::If> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        self.cond.lower(srcmap, scope_map, tcx)?;
        self.then.lower(srcmap, scope_map, tcx)?;
        self.els.lower(srcmap, scope_map, tcx)
    }
}

impl LowerAST for ast::List {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        self.items.lower(srcmap, scope_map, tcx)
    }
}

impl LowerAST for Sourced<'_, ast::Name> {
    type Output = ();

    fn lower(
        &mut self,
        _: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        let name = self.path.to_string();
        let scopes = scope_map.get(self.src_module()).unwrap();
        log::debug!("looking for name `{}` in scopes: {:?}", name, scopes);
        if let Some(fqn) = tcx.resolve_name(scopes, &name) {
            log::debug!("fqn for `{}`: {}", name, fqn);
            self.path = fqn.clone();
        }
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::Pattern> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        let (value, src) = self.unpack_mut();
        match value {
            ast::Pattern::Name(n) | ast::Pattern::Deref(n) => {
                Sourced(n, src).lower(srcmap, scope_map, tcx)?
            }
            ast::Pattern::Sequence(_) => todo!(),
            ast::Pattern::Tuple(_) => todo!(),
        }

        Ok(())
    }
}

impl LowerAST for ast::Range {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        self.start.lower(srcmap, scope_map, tcx)?;
        self.end.lower(srcmap, scope_map, tcx)
    }
}

impl LowerAST for ast::Sequence {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        self.items.lower(srcmap, scope_map, tcx)
    }
}

impl LowerAST for ast::Tuple {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        self.seq.lower(srcmap, scope_map, tcx)
    }
}

impl LowerAST for Sourced<'_, ast::UnaryOp> {
    type Output = ast::Call;

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        let (unop, src) = self.unpack_mut();
        let mut expr = unop.expr.as_ref().clone();
        expr.lower(srcmap, scope_map, tcx)?;
        let name = unop.op.to_string();
        let fqn = Path::from(name);
        // let fqn = if let Some(fqn) = tcx.lookup_fqn(&name) {
        //     fqn.clone()
        // } else {
        //     Path::from(name)
        // };

        let op_var = Node::new(Expr::Path(fqn));
        srcmap.set_src(&op_var, src.respan(unop.op_span));

        Ok(Call::new(op_var, vec![expr]))
    }
}

impl LowerAST for Sourced<'_, ast::While> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        self.cond.lower(srcmap, scope_map, tcx)?;
        self.body.lower(srcmap, scope_map, tcx)
    }
}

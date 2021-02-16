use std::{
    collections::{HashMap, HashSet},
    ops::{Deref, DerefMut},
};

use ast::{Call, Impl};

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
    utils::{self, try_replace},
};

use super::{Decl, Expr, Extern, Fn, Modifier, Name, Node, Path, Struct, Trait, TypeParams};

fn get_ty_vars(
    ty_params: Option<&TypeParams>,
    scope: &Path,
    filepath: &FilePath,
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

    pub fn value_mut(&mut self) -> &mut T {
        &mut self.0
    }

    pub fn info(&self) -> &Source {
        &self.1
    }

    pub fn src(&self) -> &Source {
        &self.1
    }

    pub fn path(&self) -> &Path {
        &self.1.path
    }
}

pub trait LowerAST
where
    Self: Sized,
{
    type Output;

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output>;
}

impl<T, U> LowerAST for Box<T>
where
    T: LowerAST<Output = U>,
{
    type Output = U;

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<U> {
        self.as_mut().lower(srcmap, tcx)
    }
}

impl<T, U> LowerAST for Option<T>
where
    T: LowerAST<Output = U>,
{
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<()> {
        if let Some(v) = self {
            v.lower(srcmap, tcx)?;
        }
        Ok(())
    }
}

impl<T, U> LowerAST for Vec<T>
where
    T: LowerAST<Output = U>,
{
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<()> {
        for t in self.iter_mut() {
            t.lower(srcmap, tcx)?;
        }
        Ok(())
    }
}

impl LowerAST for Node<Decl> {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<()> {
        let src = srcmap.get(self);
        let scope = &src.path;
        let decl = &mut self.value;
        match decl {
            Decl::Extern(decl) => {
                Sourced(decl, &src).lower(srcmap, tcx)?;
            }
            Decl::Mutable(n) | Decl::Name(n) => {
                if let Some(ty) = n.value.ty.as_deref_mut() {
                    ty.resolve_ty(scope, tcx);
                }
                let ty = n.ty.as_deref().unwrap().clone();
                tcx.bind_var(&n.path, ty);
            }
            d @ Decl::Declare(_) => unimplemented!("decl to type: {}", d),
            Decl::Fn(func) => Sourced(func, &src).lower(srcmap, tcx)?,
            Decl::FnSig(sig) => todo!("lower: Decl::FnSig: {:?}", sig),
            Decl::Struct(st) => Sourced(st, &src).lower(srcmap, tcx)?,
            Decl::Trait(tr) => Sourced(tr, &src).lower(srcmap, tcx)?,
            Decl::TypeAlias(name, ty) => todo!("lower: Decl::TypeAlias: {:?} = {:?}", name, ty),
            Decl::Impl(im) => Sourced(im, &src).lower(srcmap, tcx)?,
        };
        Ok(())
    }
}

impl LowerAST for Sourced<'_, Extern> {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<()> {
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

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<()> {
        let (st, src) = self.unpack_mut();
        let name = st.name.to_string();
        let struct_path = if Ty::is_builtin(&name) {
            Path::from(name.clone())
        } else {
            src.path.clone()
        };

        let mut struct_ctx = tcx.clone();
        let ty_vars = get_ty_vars(
            st.ty_params.as_ref(),
            &struct_path,
            &src.filepath,
            &mut struct_ctx,
        )?;

        let mut fields_vec = vec![];
        let mut field_tys = vec![];
        if let Some(fields) = &st.fields {
            for field in fields.iter() {
                let ty = if let Some(ty) = &field.ty {
                    let mut ty = ty.clone_value();
                    ty.resolve_ty(&struct_path, &mut struct_ctx);
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
            field_tys.clone(),
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

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        let (tr, src) = self.unpack_mut();
        let scope = &src.path;
        let ty_span = *tr.ty.span().unwrap();
        let parent_scope = scope.parent();
        tr.ty.resolve_ty(scope, tcx);

        let (name, ty_params) = match tr.ty.deref() {
            Ty::Projection(n, tp, _) => (n.clone(), tp.clone()),
            t @ _ => {
                return Err(RayError {
                    msg: format!("expected trait type name with parameters but found `{}`", t),
                    src: vec![Source::new(src.filepath.clone(), ty_span, Path::new())],
                    kind: RayErrorKind::Type,
                })
            }
        };

        // traits should only have one type parameter
        if ty_params.len() != 1 {
            return Err(RayError {
                msg: format!("expected one type parameter but found {}", ty_params.len()),
                src: vec![Source::new(src.filepath.clone(), ty_span, Path::new())],
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
                src: vec![Source::new(src.filepath.clone(), ty_span, Path::new())],
                kind: RayErrorKind::Type,
            });
        }

        let base_ty = tp.clone();
        let base_ty_fqn = base_ty.get_path().unwrap();
        let trait_ty = Ty::Projection(fqn.clone(), ty_params, vec![]);

        let mut fields = vec![];
        for func in tr.funcs.iter_mut() {
            let func_name = match &func.name {
                Some(n) => n.clone(),
                _ => {
                    return Err(RayError {
                        msg: format!("trait function on `{}` does not have a name", tr.ty),
                        src: vec![Source::new(src.filepath.clone(), func.span, Path::new())],
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

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        let (imp, src) = self.unpack_mut();
        let scope = &src.path;
        let parent_scope = scope.parent();
        imp.ty.resolve_ty(scope, tcx);

        let (trait_name, ty_params) = match imp.ty.deref() {
            Ty::Projection(name, ty_params, _) => (name.clone(), ty_params.clone()),
            t => {
                return Err(RayError {
                    msg: format!("`{}` is not a valid trait", t),
                    src: vec![Source::new(
                        src.filepath.clone(),
                        *imp.ty.span().unwrap(),
                        Path::new(),
                    )],
                    kind: RayErrorKind::Type,
                })
            }
        };

        // traits should only have one type parameter
        if ty_params.len() != 1 {
            return Err(RayError {
                msg: format!("expected one type argument but found {}", ty_params.len()),
                src: vec![Source::new(
                    src.filepath.clone(),
                    *imp.ty.span().unwrap(),
                    Path::new(),
                )],
                kind: RayErrorKind::Type,
            });
        }

        // lookup the trait in the context
        let trait_fqn = Path::from(trait_name.as_str());
        let trait_ty = match tcx.get_trait_ty(&trait_fqn) {
            Some(t) => t.clone(),
            _ => {
                return Err(RayError {
                    msg: format!("trait `{}` is not defined", trait_fqn),
                    src: vec![Source::new(
                        src.filepath.clone(),
                        *imp.ty.span().unwrap(),
                        Path::new(),
                    )],
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
                    src: vec![Source::new(
                        src.filepath.clone(),
                        *imp.ty.span().unwrap(),
                        Path::new(),
                    )],
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
                                src: vec![Source::new(
                                    src.filepath.clone(),
                                    f.sig.span,
                                    Path::new(),
                                )],
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
                func.lower(srcmap, tcx)?;
            }
        }

        if let Some(ext) = &mut imp.externs {
            for e in ext {
                let name = e.get_name().unwrap();
                impl_set.insert(name);
                e.lower(srcmap, tcx)?;
            }
        }

        // make sure that everything has been implemented
        for (n, _) in trait_ty.fields.iter() {
            if !impl_set.contains(n) {
                return Err(RayError {
                    msg: format!("trait implementation is missing for field `{}`", n),
                    src: vec![Source::new(
                        src.filepath.clone(),
                        *imp.ty.span().unwrap(),
                        Path::new(),
                    )],
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

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<()> {
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

        let mut func_fqn = Path::from(name.clone());
        if func_fqn.len() == 1 {
            func_fqn = src.path.clone();
        }

        tcx.add_fqn(name.clone(), func_fqn.clone());

        let mut fn_ctx = tcx.clone();
        let mut param_tys = vec![];
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

            let param_ty = p.ty().cloned();
            if param_ty.is_some() {
                num_typed += 1;
            }

            param_tys.push(param_ty);
        }

        if num_typed != 0 && num_typed != param_tys.len() {
            panic!("cannot infer type of only some parameters");
        }

        if num_typed == param_tys.len() {
            func.sig.ty = Some(Ty::from_sig(
                &func.sig,
                &func_fqn,
                &src.filepath,
                &mut fn_ctx,
                tcx,
                srcmap,
            )?);
        }

        func.body.lower(srcmap, tcx)?;

        Ok(())
    }
}

impl LowerAST for Node<Expr> {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<()> {
        let src = srcmap.get(self);
        let new_value = match &mut self.value {
            Expr::Assign(assign) => return assign.lower(srcmap, tcx),
            Expr::Asm(asm) => return Sourced(asm, &src).lower(srcmap, tcx),
            Expr::BinOp(b) => {
                let call = Sourced(b, &src).lower(srcmap, tcx)?;
                Expr::Call(call)
            }
            Expr::Block(b) => return b.lower(srcmap, tcx),
            Expr::Break(_) => todo!("lower: Expr::Break: {:?}", self),
            Expr::Call(c) => return c.lower(srcmap, tcx),
            Expr::Cast(c) => return Sourced(c, &src).lower(srcmap, tcx),
            Expr::Closure(_) => todo!("lower: Expr::Closure: {:?}", self),
            Expr::Curly(c) => return Sourced(c, &src).lower(srcmap, tcx),
            Expr::DefaultValue(_) => todo!("lower: Expr::DefaultValue: {:?}", self),
            Expr::Dot(d) => return d.lower(srcmap, tcx),
            Expr::Fn(_) => todo!("lower: Expr::Fn: {:?}", self),
            Expr::For(_) => todo!("lower: Expr::For: {:?}", self),
            Expr::If(_) => todo!("lower: Expr::If: {:?}", self),
            Expr::Index(_) => todo!("lower: Expr::Index: {:?}", self),
            Expr::Labeled(_, _) => todo!("lower: Expr::Labeled: {:?}", self),
            Expr::List(l) => return l.lower(srcmap, tcx),
            Expr::Literal(_) => return Ok(()),
            Expr::Loop(_) => todo!("lower: Expr::Loop: {:?}", self),
            Expr::Name(n) => return n.lower(srcmap, tcx),
            Expr::Path(p) => return Ok(()),
            Expr::Paren(ex) => return ex.lower(srcmap, tcx),
            Expr::Range(r) => return r.lower(srcmap, tcx),
            Expr::Return(_) => todo!("lower: Expr::Return: {:?}", self),
            Expr::Sequence(seq) => return seq.lower(srcmap, tcx),
            Expr::Tuple(t) => return t.lower(srcmap, tcx),
            Expr::Type(_) => todo!("lower: Expr::Type: {:?}", self),
            Expr::TypeAnnotated(ex, ty) => {
                ty.resolve_ty(&src.path, tcx);
                return ex.lower(srcmap, tcx);
            }
            Expr::UnaryOp(u) => {
                let call = Sourced(u, &src).lower(srcmap, tcx)?;
                Expr::Call(call)
            }
            Expr::Unsafe(_) => todo!("lower: Expr::Unsafe: {:?}", self),
            Expr::While(_) => todo!("lower: Expr::While: {:?}", self),
        };

        let _ = std::mem::replace(&mut self.value, new_value);
        Ok(())
    }
}

impl LowerAST for ast::Assign {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<()> {
        fn convert_assign_op(
            op: &ast::InfixOp,
            op_span: Span,
            lhs_operand: (u64, Expr),
            mut rhs_operand: Node<Expr>,
            srcmap: &mut SourceMap,
            tcx: &mut TyCtx,
        ) -> RayResult<Node<Expr>> {
            let (lhs_id, lhs_value) = lhs_operand;
            let lhs_operand = Node {
                id: lhs_id,
                value: lhs_value,
            };

            let lhs_src = srcmap.get(&lhs_operand);
            let rhs_src = srcmap.get(&rhs_operand);

            rhs_operand.lower(srcmap, tcx)?;
            let name = op.to_string();
            let fqn = if let Some(fqn) = tcx.lookup_fqn(&name) {
                fqn.clone()
            } else {
                Path::from(name)
            };

            let op_var = Node::new(Expr::Path(fqn));
            srcmap.set_src(&op_var, rhs_src.respan(op_span));

            let src = lhs_src.extend_to(&rhs_src);
            let node = Node::new(Expr::Call(ast::Call {
                lhs: Box::new(op_var),
                args: ast::Sequence::new(vec![lhs_operand, rhs_operand]),
                args_span: Span::new(),
                paren_span: Span::new(),
            }));

            srcmap.set_src(&node, src);
            Ok(node)
        }

        let (lhs_id, lhs_value) = self.lhs.clone().unpack();
        let lhs = match lhs_value {
            ast::Pattern::Name(n) => n.path.clone(),
            l => unimplemented!("converting lhs of self to infer expr: {}", l),
        };

        if let ast::InfixOp::AssignOp(op) = self.op.clone() {
            let op_span = self.op_span;
            try_replace::<_, _, RayError>(&mut self.rhs, |rhs| {
                Ok(Box::new(convert_assign_op(
                    &op,
                    op_span,
                    (lhs_id, Expr::Path(lhs.clone())),
                    *rhs,
                    srcmap,
                    tcx,
                )?))
            })?;
        } else {
            self.rhs.lower(srcmap, tcx)?;
        };

        if matches!(self.op, ast::InfixOp::AssignOp(_)) {
            self.op = ast::InfixOp::Assign;
        }

        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::asm::Asm> {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<()> {
        let (asm, info) = self.unpack_mut();
        let scope = &info.path;
        asm.ret_ty.as_deref_mut().map(|t| t.resolve_ty(scope, tcx));
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::BinOp> {
    type Output = ast::Call;

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        let (binop, src) = self.unpack_mut();
        let mut lhs = binop.lhs.as_ref().clone();
        lhs.lower(srcmap, tcx)?;
        let mut rhs = binop.rhs.as_ref().clone();
        rhs.lower(srcmap, tcx)?;

        let name = binop.op.to_string();
        let fqn = if let Some(fqn) = tcx.lookup_fqn(&name) {
            fqn.clone()
        } else {
            Path::from(name)
        };

        let op_var = Node::new(Expr::Path(fqn));
        srcmap.set_src(&op_var, src.respan(binop.op_span));

        Ok(Call::new(op_var, vec![lhs, rhs]))
    }
}

impl LowerAST for ast::Block {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        self.stmts.lower(srcmap, tcx)
    }
}

impl LowerAST for ast::Call {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        self.lhs.lower(srcmap, tcx)?;
        self.args.items.lower(srcmap, tcx)
    }
}

impl LowerAST for Sourced<'_, ast::Cast> {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        let (cast, info) = self.unpack_mut();
        cast.lhs.lower(srcmap, tcx)?;
        cast.ty.resolve_ty(&info.path, tcx);
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::Curly> {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
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

        let filepath = src.filepath.clone();
        let mut param_map = vec![];
        for el in curly.elements.drain(..) {
            let el_span = srcmap.span_of(&el);
            let (n, name_span, el) = match el.value {
                ast::CurlyElement::Name(n) => (n.clone(), el_span, Node::new(Expr::Name(n))),
                ast::CurlyElement::Labeled(n, ex) => (n, el_span, ex),
            };

            let field_str = n.to_string();
            if let Some(i) = idx.get(&field_str) {
                param_map.push((*i, n.clone(), el));
            } else {
                return Err(RayError {
                    msg: format!("struct `{}` does not have field `{}`", lhs, n),
                    src: vec![Source::new(filepath, name_span, Path::new())],
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

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        self.lhs.lower(srcmap, tcx)
    }
}

impl LowerAST for ast::List {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        self.items.lower(srcmap, tcx)
    }
}

impl LowerAST for ast::Name {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        let name = self.path.to_string();
        if let Some(fqn) = tcx.lookup_fqn(&name) {
            log::debug!("fqn for `{}`: {}", name, fqn);
            self.path = fqn.clone();
        }
        Ok(())
    }
}

impl LowerAST for ast::Range {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        self.start.lower(srcmap, tcx)?;
        self.end.lower(srcmap, tcx)
    }
}

impl LowerAST for ast::Sequence {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        self.items.lower(srcmap, tcx)
    }
}

impl LowerAST for ast::Tuple {
    type Output = ();

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        self.seq.lower(srcmap, tcx)
    }
}

impl LowerAST for Sourced<'_, ast::UnaryOp> {
    type Output = ast::Call;

    fn lower(&mut self, srcmap: &mut SourceMap, tcx: &mut TyCtx) -> RayResult<Self::Output> {
        let (unop, src) = self.unpack_mut();
        let mut expr = unop.expr.as_ref().clone();
        expr.lower(srcmap, tcx)?;
        let name = unop.op.to_string();
        let fqn = if let Some(fqn) = tcx.lookup_fqn(&name) {
            fqn.clone()
        } else {
            Path::from(name)
        };

        let op_var = Node::new(Expr::Path(fqn));
        srcmap.set_src(&op_var, src.respan(unop.op_span));

        Ok(Call::new(op_var, vec![expr]))
    }
}

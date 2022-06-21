use std::{
    collections::{HashMap, HashSet},
    ops::{Deref, DerefMut},
};

use ast::Impl;
use top::{directives::TypeClassDirective, Predicate, Predicates, Substitutable};

use crate::{
    ast::{self, TraitDirectiveKind},
    errors::{RayError, RayErrorKind, RayResult},
    pathlib::FilePath,
    span::{parsed::Parsed, Source, SourceMap},
    subst,
    typing::{
        info::TypeSystemInfo,
        ty::{ImplTy, StructTy, TraitTy, Ty, TyScheme, TyVar},
        TyCtx,
    },
    utils::try_replace,
};

use super::{Decl, Expr, Extern, Func, Modifier, Node, Path, Struct, Trait, TypeParams};

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
            ty.resolve_fqns(scope, tcx);
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

    ty_vars.sort();
    ty_vars.dedup();

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
                if let Some(ty) = n.ty.as_deref_mut() {
                    ty.resolve_fqns(scope, tcx);
                }
                // TODO: what do we do here?
                let ty = n.ty.as_deref().unwrap().clone();
            }
            d @ Decl::Declare(_) => unimplemented!("decl to type: {}", d),
            Decl::Func(func) => Sourced(func, &src).lower(srcmap, scope_map, tcx)?,
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
                        msg: str!("externed function must have a name"),
                        src: vec![src.clone()],
                        kind: RayErrorKind::Type,
                    })?
                    .clone();
                sig.path = Path::from(name);

                // make sure that the signature is fully typed
                let mut fn_tcx = tcx.clone();
                fn_tcx.resolve_signature(sig, &src.path, &src.filepath, srcmap)?;

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

        let mut fields = vec![];
        let mut field_tys = vec![];
        if let Some(struct_fields) = &st.fields {
            for field in struct_fields.iter() {
                let ty = if let Some(ty) = &field.ty {
                    let mut ty = ty.clone_value();
                    ty.resolve_fqns(&struct_path, &mut struct_tcx);
                    ty
                } else {
                    let src = srcmap.get(field);
                    return Err(RayError {
                        msg: format!("struct field on `{}` does not have a type", st.name),
                        src: vec![src],
                        kind: RayErrorKind::Type,
                    });
                };

                fields.push((field.path.to_string(), ty.clone()));
                field_tys.push(ty);
            }
        }

        let ty = Ty::with_vars(&struct_path, &ty_vars);
        let struct_ty = TyScheme::new(ty_vars, Predicates::new(), ty);
        tcx.add_struct_ty(
            name,
            StructTy {
                path: struct_path,
                ty: struct_ty,
                fields,
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
        let trait_fqn = &src.path;
        let ty_span = *tr.ty.span().unwrap();
        let parent_scope = trait_fqn.parent();
        tr.ty.resolve_fqns(trait_fqn, tcx);

        let (name, mut ty_params) = match tr.ty.deref() {
            Ty::Projection(n, tp) => (n.name(), tp.clone()),
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

        let fqn = trait_fqn.to_string();
        let mut trait_tcx = tcx.clone();
        ty_params
            .iter_mut()
            .for_each(|t| t.map_vars(&mut trait_tcx));

        let mut ty_vars = vec![];
        let tp = &ty_params[0];
        if let Ty::Var(v) = tp {
            ty_vars.push(v.clone());
        } else {
            return Err(RayError {
                msg: format!("expected a type parameter but found {}", tp),
                src: vec![src.respan(ty_span)],
                kind: RayErrorKind::Type,
            });
        }

        let base_ty = tp.clone();
        let trait_ty = Ty::with_tys(&fqn, ty_params.clone());

        let mut fields = vec![];
        for func in tr.fields.iter_mut() {
            let sig = variant!(func.deref_mut(), if Decl::FnSig(sig));
            let func_name = match &sig.name {
                Some(n) => n.clone(),
                _ => {
                    return Err(RayError {
                        msg: format!("trait function on `{}` does not have a name", tr.ty),
                        src: vec![src.respan(sig.span)],
                        kind: RayErrorKind::Type,
                    })
                }
            };

            let mut fn_tcx = trait_tcx.clone();
            fn_tcx.resolve_signature(sig, trait_fqn, &src.filepath, srcmap)?;

            // add the trait type to the qualifiers
            let scheme = sig.ty.as_mut().unwrap();
            let base_ty = base_ty.clone();
            scheme
                .ty
                .qualifiers_mut()
                .insert(0, Predicate::class(trait_fqn.to_string(), base_ty.clone()));

            log::debug!("trait func scheme = {:?}", scheme);

            let (param_tys, _) = scheme.unquantified().ty().try_borrow_fn()?;
            let func_fqn = trait_fqn.append_type_args(&ty_params).append(&func_name);
            log::debug!("add fqn: {} => {}", func_name, func_fqn);

            if param_tys.len() == 2 && ast::InfixOp::is(&func_name) {
                tcx.add_infix_op(func_name.clone(), func_fqn.clone(), trait_fqn.clone());
            } else if param_tys.len() == 1 && ast::PrefixOp::is(&func_name) {
                tcx.add_prefix_op(func_name.clone(), func_fqn.clone(), trait_fqn.clone());
            } else {
                tcx.add_fqn(func_name.clone(), func_fqn.clone(), Some(trait_fqn.clone()));
            }

            // tcx.bind_var(func_fqn.to_string(), ty.clone());

            fields.push((func_name.clone(), scheme.clone()));

            sig.path = func_fqn;
        }

        let super_trait = tr.super_trait.clone().map(|ty| {
            let mut ty = ty.take_value();
            ty.resolve_fqns(&parent_scope, tcx);
            ty
        });

        let directives = tr
            .directives
            .iter()
            .map(|directive| match directive.kind {
                TraitDirectiveKind::Default => {
                    let args = directive
                        .args
                        .iter()
                        .map(|arg| arg.value().clone())
                        .collect();
                    TypeClassDirective::Default(
                        trait_fqn.to_string(),
                        args,
                        TypeSystemInfo::default(),
                    )
                }
            })
            .collect();

        tcx.add_trait_ty(
            name,
            TraitTy {
                path: trait_fqn.clone(),
                ty: trait_ty,
                super_traits: super_trait.map(|s| vec![s]).unwrap_or_default(),
                fields,
                directives,
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
        imp.ty.resolve_fqns(scope, tcx);

        let (trait_name, ty_params) = match imp.ty.deref() {
            Ty::Projection(ty, ty_params) => (ty.name(), ty_params.clone()),
            t => {
                return Err(RayError {
                    msg: format!(
                        "`{}` is not a valid {}",
                        t,
                        if imp.is_object { "object" } else { "trait" }
                    ),
                    src: vec![src.respan(*imp.ty.span().unwrap())],
                    kind: RayErrorKind::Type,
                })
            }
        };

        // traits should only have one type parameter
        if !imp.is_object && ty_params.len() != 1 {
            return Err(RayError {
                msg: format!("expected one type argument but found {}", ty_params.len()),
                src: vec![src.respan(*imp.ty.span().unwrap())],
                kind: RayErrorKind::Type,
            });
        }

        // lookup the trait in the context
        let trait_fqn = Path::from(trait_name.as_str());
        log::debug!("found fqn: {}", trait_fqn);
        let trait_ty = if imp.is_object {
            // we construct a special "object" trait for object implementations
            TraitTy {
                path: Path::from("core::object"),
                ty: Ty::Projection(
                    Box::new(Ty::Const(str!("object"))),
                    vec![Ty::var("core::object::'a")],
                ),
                super_traits: vec![],
                fields: vec![],
                directives: vec![],
            }
        } else {
            match tcx.get_trait_ty(&trait_fqn) {
                Some(t) => t.clone(),
                _ => {
                    return Err(RayError {
                        msg: format!("trait `{}` is not defined", trait_fqn),
                        src: vec![src.respan(*imp.ty.span().unwrap())],
                        kind: RayErrorKind::Type,
                    })
                }
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

        let base_ty = if imp.is_object {
            imp.ty.deref().clone()
        } else {
            ty_params[0].clone()
        };
        let impl_scope = base_ty.get_path().unwrap();
        log::debug!("impl fqn: {}", impl_scope);
        let mut impl_ctx = tcx.clone();
        let mut impl_set = HashSet::new();

        // consts have to be first in case they're used inside of functions
        if let Some(consts) = &mut imp.consts {
            for const_node in consts {
                const_node.lower(srcmap, scope_map, tcx)?;
                let path = const_node.lhs.path_mut().unwrap();
                let name = path.name().unwrap();
                *path = impl_scope.append(&name);
                tcx.nametree_mut().add_full_name(&path.to_vec());
            }
        }

        if let Some(funcs) = &mut imp.funcs {
            for func in funcs {
                let func_name = match &func.sig.name {
                    Some(n) => n.clone(),
                    _ => {
                        return Err(RayError {
                            msg: format!("trait function on `{}` does not have a name", trait_name),
                            src: vec![src.respan(func.sig.span)],
                            kind: RayErrorKind::Type,
                        })
                    }
                };

                // make this a fully-qualified name
                func.sig.path = if imp.is_object {
                    trait_fqn.append(&func_name)
                } else {
                    trait_fqn.append_type_args(&ty_params).append(&func_name)
                };
                log::debug!("func fqn: {}", func.sig.path);
                tcx.nametree_mut().add_full_name(&func.sig.path.to_vec());

                impl_set.insert(func_name);
                let src = srcmap.get(&func);
                Sourced(&mut func.value, &src).lower(srcmap, scope_map, tcx)?;
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

        // create a subst mapping the type parameter to the argument
        let sub = subst! { ty_param => base_ty.clone() };
        let mut trait_ty = trait_ty.ty.clone();
        trait_ty.apply_subst(&sub);
        let mut predicates = vec![];
        for q in imp.qualifiers.iter() {
            predicates.push(predicate_from_ast_ty(
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

impl LowerAST for Sourced<'_, Func> {
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
            tcx.add_fqn(name, fqn.clone(), None);
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
            // TODO: this should be an error
            panic!("cannot infer type of only some parameters");
        }

        if num_typed != 0 && num_typed == func.sig.params.len() {
            fn_tcx.resolve_signature(&mut func.sig, &func_fqn, &src.filepath, srcmap)?;
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
        match &mut self.value {
            Expr::Assign(assign) => assign.lower(srcmap, scope_map, tcx),
            Expr::Asm(asm) => Sourced(asm, &src).lower(srcmap, scope_map, tcx),
            Expr::BinOp(b) => Sourced(b, &src).lower(srcmap, scope_map, tcx),
            Expr::Block(b) => b.lower(srcmap, scope_map, tcx),
            Expr::Break(value) => {
                if let Some(value) = value {
                    value.lower(srcmap, scope_map, tcx)?;
                }
                Ok(())
            }
            Expr::Call(c) => c.lower(srcmap, scope_map, tcx),
            Expr::Cast(c) => Sourced(c, &src).lower(srcmap, scope_map, tcx),
            Expr::Closure(_) => todo!("lower: Expr::Closure: {:?}", self),
            Expr::Curly(c) => Sourced(c, &src).lower(srcmap, scope_map, tcx),
            Expr::DefaultValue(_) => todo!("lower: Expr::DefaultValue: {:?}", self),
            Expr::Dot(d) => d.lower(srcmap, scope_map, tcx),
            Expr::Func(_) => todo!("lower: Expr::Fn: {:?}", self),
            Expr::For(_) => todo!("lower: Expr::For: {:?}", self),
            Expr::If(if_ex) => Sourced(if_ex, &src).lower(srcmap, scope_map, tcx),
            Expr::Index(_) => todo!("lower: Expr::Index: {:?}", self),
            Expr::Labeled(_, _) => todo!("lower: Expr::Labeled: {:?}", self),
            Expr::List(l) => l.lower(srcmap, scope_map, tcx),
            Expr::Literal(_) => Ok(()),
            Expr::Loop(_) => Ok(()),
            Expr::Name(n) => Sourced(n, &src).lower(srcmap, scope_map, tcx),
            Expr::New(n) => Sourced(n, &src).lower(srcmap, scope_map, tcx),
            Expr::Pattern(p) => Sourced(p, &src).lower(srcmap, scope_map, tcx),
            Expr::Path(p) => Sourced(p, &src).lower(srcmap, scope_map, tcx),
            Expr::Paren(ex) => ex.lower(srcmap, scope_map, tcx),
            Expr::Range(r) => r.lower(srcmap, scope_map, tcx),
            Expr::Return(_) => todo!("lower: Expr::Return: {:?}", self),
            Expr::Sequence(seq) => seq.lower(srcmap, scope_map, tcx),
            Expr::Tuple(t) => t.lower(srcmap, scope_map, tcx),
            Expr::Type(_) => todo!("lower: Expr::Type: {:?}", self),
            Expr::TypeAnnotated(ex, ty) => {
                todo!()
                // ty.resolve_ty(&src.path, tcx);
                // ex.lower(srcmap, scope_map, tcx)
            }
            Expr::UnaryOp(u) => Sourced(u, &src).lower(srcmap, scope_map, tcx),
            Expr::Unsafe(_) => todo!("lower: Expr::Unsafe: {:?}", self),
            Expr::While(w) => Sourced(w, &src).lower(srcmap, scope_map, tcx),
        }
    }
}

impl LowerAST for ast::Assign {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<()> {
        if let ast::InfixOp::AssignOp(op) = &mut self.op {
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

            let new_op = Node::new(ast::InfixOp::Assign);
            let op_src = srcmap.get(op);
            srcmap.set_src(&new_op, op_src);

            let op = std::mem::replace(op.as_mut(), new_op);
            try_replace::<_, _, RayError>(&mut self.rhs, |mut rhs| {
                rhs.lower(srcmap, scope_map, tcx)?;

                let lhs_src = srcmap.get(&lhs);
                let rhs_src = srcmap.get(&rhs);
                let src = lhs_src.extend_to(&rhs_src);
                let node = Node::new(Expr::BinOp(ast::BinOp {
                    lhs: Box::new(lhs),
                    rhs,
                    op,
                }));
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
        asm.ret_ty
            .as_deref_mut()
            .map(|t| t.resolve_fqns(scope, tcx));
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::BinOp> {
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        let (binop, _) = self.unpack_mut();
        binop.lhs.lower(srcmap, scope_map, tcx)?;
        binop.rhs.lower(srcmap, scope_map, tcx)?;
        log::debug!("lowered binop: {:?}", binop);
        Ok(())
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
        self.callee.lower(srcmap, scope_map, tcx)?;
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
        cast.ty.resolve_fqns(&info.path, tcx);
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

impl LowerAST for Sourced<'_, ast::New> {
    type Output = ();

    fn lower(
        &mut self,
        _: &mut SourceMap,
        _: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        let (new, src) = self.unpack_mut();
        let scope = &src.path;
        new.ty.resolve_fqns(scope, tcx);
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::Path> {
    type Output = ();

    fn lower(
        &mut self,
        _: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        let scopes = scope_map.get(self.src_module()).unwrap();
        log::debug!(
            "looking for name `{}` in scopes: {:?}",
            self.deref().deref(),
            scopes
        );
        if let Some(fqn) = tcx.resolve_path(scopes, &self) {
            log::debug!("fqn for `{}`: {}", self.deref().deref(), fqn);
            *self.deref_mut() = fqn.clone();
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
    type Output = ();

    fn lower(
        &mut self,
        srcmap: &mut SourceMap,
        scope_map: &HashMap<Path, Vec<Path>>,
        tcx: &mut TyCtx,
    ) -> RayResult<Self::Output> {
        let (unop, _) = self.unpack_mut();
        unop.expr.lower(srcmap, scope_map, tcx)?;
        Ok(())
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

pub fn predicate_from_ast_ty(
    q: &Parsed<Ty>,
    scope: &ast::Path,
    filepath: &FilePath,
    tcx: &mut TyCtx,
) -> Result<Predicate<Ty, TyVar>, RayError> {
    // resolve the type
    let ty_span = *q.span().unwrap();
    let q = q.clone_value();
    let (s, v) = match q {
        Ty::Projection(s, v) => (s.name(), v),
        _ => {
            return Err(RayError {
                msg: str!("qualifier must be a trait type"),
                src: vec![Source {
                    span: Some(ty_span),
                    filepath: filepath.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Type,
            })
        }
    };

    if v.len() != 1 {
        return Err(RayError {
            msg: format!("traits must have one type argument, but found {}", v.len()),
            src: vec![Source {
                span: Some(ty_span),
                filepath: filepath.clone(),
                ..Default::default()
            }],
            kind: RayErrorKind::Type,
        });
    }

    let fqn = Path::from(s.as_str());
    log::debug!("converting from ast type: {}", fqn);
    let trait_ty = match tcx.get_trait_ty(&fqn) {
        Some(t) => t,
        _ => {
            return Err(RayError {
                msg: format!("trait `{}` is not defined", fqn),
                src: vec![Source {
                    span: Some(ty_span),
                    filepath: filepath.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Type,
            })
        }
    };

    let mut trait_ty = trait_ty.ty.clone();
    let mut ty_arg = v[0].clone();
    ty_arg.map_vars(tcx);
    let ty_param = variant!(trait_ty.get_ty_param_at(0).clone(), if Ty::Var(t));
    let sub = subst! { ty_param.clone() => ty_arg.clone() };
    trait_ty.apply_subst(&sub);
    let fqn = trait_ty.get_path().unwrap();
    Ok(Predicate::class(fqn.to_string(), ty_arg))
}

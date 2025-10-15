use std::{
    collections::{HashMap, HashSet},
    ops::{Deref, DerefMut},
    vec,
};

use ast::Impl;
use top::{directives::TypeClassDirective, Predicate, Predicates, Substitutable};

use crate::{
    ast::{self, TraitDirectiveKind},
    collections::nametree::Scope,
    errors::{RayError, RayErrorKind, RayResult},
    pathlib::FilePath,
    sema::NameContext,
    span::{parsed::Parsed, Source, SourceMap, Sourced},
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
    scopes: &Vec<Scope>,
    filepath: &FilePath,
    src_module: &Path,
    ncx: &NameContext,
) -> Result<Vec<TyVar>, RayError> {
    let mut ty_vars = vec![];
    if let Some(ty_params) = ty_params {
        for tp in ty_params.tys.iter() {
            let mut ty = tp.clone_value();
            ty.resolve_fqns(scopes, ncx);
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

#[derive(Debug, Clone)]
pub struct Ident {
    is_mut: bool,
    is_lvalue: bool,
    in_current_scope: bool,
}

#[derive(Debug, Default)]
pub struct IdentMap(HashMap<Path, Ident>);

impl Deref for IdentMap {
    type Target = HashMap<Path, Ident>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for IdentMap {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Clone for IdentMap {
    fn clone(&self) -> Self {
        IdentMap(
            self.0
                .iter()
                .map(|(p, id)| {
                    let mut id = id.clone();
                    id.in_current_scope = false;
                    (p.clone(), id.clone())
                })
                .collect(),
        )
    }
}

pub struct LowerCtx<'a> {
    srcmap: &'a mut SourceMap,
    scope_map: &'a HashMap<Path, Vec<Scope>>,
    tcx: &'a mut TyCtx,
    ncx: &'a mut NameContext,
    identifiers: IdentMap,
    errors: &'a mut Vec<RayError>,
}

impl<'a> LowerCtx<'a> {
    pub fn new(
        srcmap: &'a mut SourceMap,
        scope_map: &'a HashMap<Path, Vec<Scope>>,
        tcx: &'a mut TyCtx,
        ncx: &'a mut NameContext,
        errors: &'a mut Vec<RayError>,
    ) -> Self {
        LowerCtx {
            srcmap,
            scope_map,
            tcx,
            ncx,
            identifiers: IdentMap::default(),
            errors,
        }
    }

    pub fn with_tcx<F, A>(&mut self, tcx: TyCtx, f: F) -> A
    where
        F: FnOnce(&mut LowerCtx) -> A,
    {
        let old_tcx = std::mem::replace(self.tcx, tcx);
        let out = f(self);
        let _ = std::mem::replace(self.tcx, old_tcx);
        out
    }

    pub fn with_clone<F, A>(&mut self, f: F) -> A
    where
        F: FnOnce(&mut LowerCtx) -> A,
    {
        let mut ctx = LowerCtx {
            srcmap: self.srcmap,
            scope_map: self.scope_map,
            tcx: self.tcx,
            ncx: self.ncx,
            identifiers: self.identifiers.clone(),
            errors: self.errors,
        };
        f(&mut ctx)
    }

    #[inline(always)]
    fn get_scopes(&self, src: &Source) -> &Vec<Scope> {
        self.scope_map.get(&src.src_module).unwrap()
    }
}

pub trait LowerAST
where
    Self: Sized,
{
    type Output;

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output>;
}

impl<T, U> LowerAST for Box<T>
where
    T: LowerAST<Output = U>,
{
    type Output = U;

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<U> {
        self.as_mut().lower(ctx)
    }
}

impl<T, U> LowerAST for Option<T>
where
    T: LowerAST<Output = U>,
{
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<()> {
        if let Some(v) = self {
            v.lower(ctx)?;
        }
        Ok(())
    }
}

impl<T, U> LowerAST for Vec<T>
where
    T: LowerAST<Output = U>,
{
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<()> {
        for t in self.iter_mut() {
            t.lower(ctx)?;
        }
        Ok(())
    }
}

impl LowerAST for Node<Decl> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        let scope = &src.path;
        let decl = &mut self.value;
        match decl {
            Decl::Extern(decl) => {
                Sourced(decl, &src).lower(ctx)?;
            }
            Decl::Mutable(n) | Decl::Name(n) => {
                if let Some(ty) = n.ty.as_deref_mut() {
                    let scopes = ctx.get_scopes(&src);
                    ty.resolve_fqns(scopes, ctx.ncx);
                }
                // TODO: what do we do here?
                let ty = n.ty.as_deref().unwrap().clone();
            }
            d @ Decl::Declare(_) => unimplemented!("decl to type: {}", d),
            Decl::Func(func) => Sourced(func, &src).lower(ctx)?,
            Decl::FnSig(sig) => todo!("lower: Decl::FnSig: {:?}", sig),
            Decl::Struct(st) => Sourced(st, &src).lower(ctx)?,
            Decl::Trait(tr) => Sourced(tr, &src).lower(ctx)?,
            Decl::TypeAlias(name, ty) => todo!("lower: Decl::TypeAlias: {:?} = {:?}", name, ty),
            Decl::Impl(im) => Sourced(im, &src).lower(ctx)?,
        };
        Ok(())
    }
}

impl LowerAST for Sourced<'_, Extern> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<()> {
        let (ext, src) = self.unpack_mut();
        match ext.decl_mut() {
            Decl::Mutable(_) => todo!(),
            Decl::Name(_) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::FnSig(sig) => {
                let name = sig
                    .path
                    .name()
                    .ok_or_else(|| RayError {
                        msg: str!("externed function must have a name"),
                        src: vec![src.clone()],
                        kind: RayErrorKind::Type,
                    })?
                    .clone();
                sig.path = Path::from(name);

                // make sure that the signature is fully typed
                let mut fn_tcx = ctx.tcx.clone();
                let scopes = ctx.get_scopes(src);
                fn_tcx.resolve_signature(
                    sig,
                    &src.path,
                    scopes,
                    &src.filepath,
                    ctx.srcmap,
                    ctx.ncx,
                )?;

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

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<()> {
        let (st, src) = self.unpack_mut();
        let name = st.name.to_string();
        let struct_path = if Ty::is_builtin(&name) {
            Path::from(name.clone())
        } else {
            src.path.clone()
        };

        let mut struct_tcx = ctx.tcx.clone();
        let scopes = ctx.get_scopes(src);
        let ty_vars = get_ty_vars(
            st.ty_params.as_ref(),
            scopes, //&struct_path,
            &src.filepath,
            &src.src_module,
            ctx.ncx,
        )?;

        let mut fields = vec![];
        let mut field_tys = vec![];
        if let Some(struct_fields) = &st.fields {
            for field in struct_fields.iter() {
                let ty = if let Some(ty) = &field.ty {
                    let mut ty = ty.clone_value();
                    ty.resolve_fqns(scopes, ctx.ncx);
                    // ty.resolve_fqns(&struct_path, ctx.ncx);
                    ty
                } else {
                    let src = ctx.srcmap.get(field);
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
        ctx.tcx.add_struct_ty(StructTy {
            path: struct_path,
            ty: struct_ty,
            fields,
        });
        Ok(())
    }
}

impl LowerAST for Sourced<'_, Trait> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        let (tr, src) = self.unpack_mut();
        let trait_fqn = &src.path;
        let ty_span = *tr.ty.span().unwrap();
        let parent_scope = trait_fqn.parent();
        let scopes = ctx.get_scopes(src);
        tr.ty.resolve_fqns(scopes, ctx.ncx);
        // tr.ty.resolve_fqns(trait_fqn, ctx.ncx);

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
        let mut trait_tcx = ctx.tcx.clone();
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
            let func_name = match sig.path.name() {
                Some(n) => n,
                _ => {
                    return Err(RayError {
                        msg: format!("trait function on `{}` does not have a name", tr.ty),
                        src: vec![src.respan(sig.span)],
                        kind: RayErrorKind::Type,
                    })
                }
            };

            let mut fn_tcx = trait_tcx.clone();
            let scopes = ctx.get_scopes(src);
            fn_tcx.resolve_signature(sig, trait_fqn, scopes, &src.filepath, ctx.srcmap, ctx.ncx)?;

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
                ctx.tcx
                    .add_infix_op(func_name.clone(), func_fqn.clone(), trait_fqn.clone());
            } else if param_tys.len() == 1 && ast::PrefixOp::is(&func_name) {
                ctx.tcx
                    .add_prefix_op(func_name.clone(), func_fqn.clone(), trait_fqn.clone());
            } else {
                log::debug!("add name in scope: {} => {}", func_name, trait_fqn);
                let scope = trait_fqn.to_name_vec();
                ctx.ncx
                    .nametree_mut()
                    .add_name_in_scope(&scope, func_name.clone())
            }

            fields.push((func_name.clone(), scheme.clone()));

            sig.path = func_fqn;
        }

        let scopes = ctx.get_scopes(src);
        let super_trait = tr.super_trait.clone().map(|ty| {
            let mut ty = ty.take_value();
            // ty.resolve_fqns(&parent_scope, ctx.ncx);
            ty.resolve_fqns(scopes, ctx.ncx);
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

        let fqn = trait_fqn.to_name_vec();
        ctx.ncx.nametree_mut().add_full_name(&fqn);
        ctx.tcx.add_trait_ty(
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

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        let (imp, src) = self.unpack_mut();
        let scope = &src.path;
        let scopes = ctx.get_scopes(src);
        imp.ty.resolve_fqns(scopes, ctx.ncx);
        // imp.ty.resolve_fqns(scope, ctx.ncx);

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
            match ctx.tcx.get_trait_ty(&trait_fqn) {
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
        let mut impl_ctx = ctx.tcx.clone();
        let mut impl_set = HashSet::new();

        // consts have to be first in case they're used inside of functions
        if let Some(consts) = &mut imp.consts {
            for const_node in consts {
                const_node.lower(ctx)?;
                let path = const_node.lhs.path_mut().unwrap();
                let name = path.name().unwrap();
                *path = impl_scope.append(&name);
                ctx.ncx.nametree_mut().add_full_name(&path.to_name_vec());
            }
        }

        if let Some(funcs) = &mut imp.funcs {
            for func in funcs {
                let func_name = match func.sig.path.name() {
                    Some(n) => n,
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
                ctx.ncx
                    .nametree_mut()
                    .add_full_name(&func.sig.path.to_name_vec());

                impl_set.insert(func_name);
                let src = ctx.srcmap.get(&func);
                Sourced(&mut func.value, &src).lower(ctx)?;
            }
        }

        if let Some(ext) = &mut imp.externs {
            for e in ext {
                let name = e.get_name().unwrap();
                impl_set.insert(name);
                e.lower(ctx)?;
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
        ctx.tcx.add_impl(trait_fqn, impl_ty);
        Ok(())
    }
}

impl LowerAST for Sourced<'_, Func> {
    type Output = ();

    fn lower<'a>(&mut self, ctx: &mut LowerCtx<'a>) -> RayResult<()> {
        let (func, src) = self.unpack_mut();
        if func.sig.is_anon {
            return Err(RayError {
                msg: format!("top-level function must have a name"),
                src: vec![src.clone()],
                kind: RayErrorKind::Name,
            });
        }

        if !func.sig.is_method {
            log::debug!("add fqn: {}", func.sig.path);
            ctx.ncx
                .nametree_mut()
                .add_full_name(&func.sig.path.to_name_vec());
        }

        let mut fn_tcx = ctx.tcx.clone();
        let num_typed = func.sig.params.iter().filter(|p| p.ty().is_some()).count();
        if num_typed != 0 && num_typed != func.sig.params.len() {
            // TODO: this should be an error
            panic!("cannot infer type of only some parameters");
        }

        if num_typed != 0 && num_typed == func.sig.params.len() {
            let fn_scope = func.sig.path.clone();
            let scopes = ctx.get_scopes(src);
            fn_tcx.resolve_signature(
                &mut func.sig,
                &fn_scope,
                scopes,
                &src.filepath,
                ctx.srcmap,
                &ctx.ncx,
            )?;
        }

        ctx.with_tcx(fn_tcx, |ctx| func.body.lower(ctx))
    }
}

impl LowerAST for Node<Expr> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        match &mut self.value {
            Expr::Assign(assign) => assign.lower(ctx),
            Expr::Asm(asm) => Sourced(asm, &src).lower(ctx),
            Expr::BinOp(b) => Sourced(b, &src).lower(ctx),
            Expr::Block(b) => b.lower(ctx),
            Expr::Break(value) => {
                if let Some(value) = value {
                    value.lower(ctx)?;
                }
                Ok(())
            }
            Expr::Call(c) => c.lower(ctx),
            Expr::Cast(c) => Sourced(c, &src).lower(ctx),
            Expr::Closure(_) => todo!("lower: Expr::Closure: {:?}", self),
            Expr::Curly(c) => Sourced(c, &src).lower(ctx),
            Expr::DefaultValue(_) => todo!("lower: Expr::DefaultValue: {:?}", self),
            Expr::Dot(d) => d.lower(ctx),
            Expr::Func(_) => todo!("lower: Expr::Fn: {:?}", self),
            Expr::For(_) => todo!("lower: Expr::For: {:?}", self),
            Expr::If(if_ex) => Sourced(if_ex, &src).lower(ctx),
            Expr::Index(_) => todo!("lower: Expr::Index: {:?}", self),
            Expr::Labeled(_, _) => todo!("lower: Expr::Labeled: {:?}", self),
            Expr::List(l) => l.lower(ctx),
            Expr::Literal(_) => Ok(()),
            Expr::Loop(_) => Ok(()),
            Expr::Name(n) => Sourced(n, &src).lower(ctx),
            Expr::New(n) => Sourced(n, &src).lower(ctx),
            Expr::Pattern(p) => Sourced(p, &src).lower(ctx),
            Expr::Path(p) => Sourced(p, &src).lower(ctx),
            Expr::Paren(ex) => ex.lower(ctx),
            Expr::Range(r) => r.lower(ctx),
            Expr::Return(_) => todo!("lower: Expr::Return: {:?}", self),
            Expr::Sequence(seq) => seq.lower(ctx),
            Expr::Tuple(t) => t.lower(ctx),
            Expr::Type(_) => todo!("lower: Expr::Type: {:?}", self),
            Expr::TypeAnnotated(ex, ty) => {
                todo!()
                // ty.resolve_ty(&src.path, tcx);
                // ex.lower(ctx)
            }
            Expr::UnaryOp(u) => Sourced(u, &src).lower(ctx),
            Expr::Unsafe(_) => todo!("lower: Expr::Unsafe: {:?}", self),
            Expr::While(w) => Sourced(w, &src).lower(ctx),
        }
    }
}

impl LowerAST for ast::Assign {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<()> {
        // check each identifier for mutability
        for id in self.lhs.identifiers() {
            let (path, is_lvalue) = id.value;
            match ctx.identifiers.get(path) {
                Some(ident) if !ident.is_mut && ident.in_current_scope => {
                    let src = ctx.srcmap.get(&id);
                    ctx.errors.push(RayError {
                        msg: format!("cannot assign to immutable identifier `{}`", path),
                        src: vec![src],
                        kind: RayErrorKind::Type,
                    });
                }
                Some(_) if is_lvalue => { /* do nothing */ }
                _ => {
                    ctx.identifiers.insert(
                        path.clone(),
                        Ident {
                            is_mut: self.is_mut,
                            is_lvalue,
                            in_current_scope: true,
                        },
                    );
                }
            }
        }

        if let ast::InfixOp::AssignOp(op) = &mut self.op {
            let lhs_src = ctx.srcmap.get(&self.lhs);
            let lhs = match self.lhs.clone().try_take_map(|pat| match pat {
                ast::Pattern::Name(n) => Ok(Expr::Name(n)),
                ast::Pattern::Sequence(_) | ast::Pattern::Tuple(_) | ast::Pattern::Deref(_) => {
                    Err(RayError {
                        msg: str!("cannot use expression as l-value for re-assignment"),
                        src: vec![lhs_src],
                        kind: RayErrorKind::Type,
                    })
                }
            }) {
                Ok(lhs) => lhs,
                Err(err) => {
                    ctx.errors.push(err);
                    return Ok(());
                }
            };

            let new_op = Node::new(ast::InfixOp::Assign);
            let op_src = ctx.srcmap.get(op);
            ctx.srcmap.set_src(&new_op, op_src);

            let op = std::mem::replace(op.as_mut(), new_op);
            try_replace(&mut self.rhs, |mut rhs| -> RayResult<_> {
                rhs.lower(ctx)?;

                let lhs_src = ctx.srcmap.get(&lhs);
                let rhs_src = ctx.srcmap.get(&rhs);
                let src = lhs_src.extend_to(&rhs_src);
                let node = Node::new(Expr::BinOp(ast::BinOp {
                    lhs: Box::new(lhs),
                    rhs,
                    op,
                }));
                ctx.srcmap.set_src(&node, src);
                Ok(Box::new(node))
            })?;
        } else {
            self.rhs.lower(ctx)?;
        };

        if matches!(self.op, ast::InfixOp::AssignOp(_)) {
            self.op = ast::InfixOp::Assign;
        }

        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::asm::Asm> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<()> {
        let (asm, src) = self.unpack_mut();
        let scope = &src.path;
        let scopes = ctx.get_scopes(src);
        asm.ret_ty
            .as_deref_mut()
            .map(|t| t.resolve_fqns(scopes, ctx.ncx));
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::BinOp> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        let (binop, _) = self.unpack_mut();
        binop.lhs.lower(ctx)?;
        binop.rhs.lower(ctx)?;
        Ok(())
    }
}

impl LowerAST for ast::Block {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        ctx.with_clone(|ctx| self.stmts.lower(ctx))
    }
}

impl LowerAST for ast::Call {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        self.callee.lower(ctx)?;
        self.args.items.lower(ctx)
    }
}

impl LowerAST for Sourced<'_, ast::Cast> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        let (cast, src) = self.unpack_mut();
        cast.lhs.lower(ctx)?;
        let scopes = ctx.get_scopes(src);
        cast.ty.resolve_fqns(scopes, ctx.ncx);
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::Curly> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        if self.lhs.is_none() {
            unimplemented!("anon struct construction: {}", self.value())
        }

        let (curly, src) = self.unpack();
        let (lhs, lhs_src) = curly.lhs.as_ref().unwrap().clone().take();
        let lhs_span = lhs_src.span.unwrap();
        let scopes = ctx.scope_map.get(self.src_module()).unwrap();
        let name = lhs.name().unwrap();
        let struct_fqn = if Ty::is_builtin(&name) {
            Path::from(name)
        } else {
            match ctx.ncx.resolve_name(scopes, &name) {
                Some(fqn) => fqn.clone(),
                _ => {
                    return Err(RayError {
                        msg: format!("struct type `{}` is undefined", lhs),
                        src: vec![src.respan(lhs_span)],
                        kind: RayErrorKind::Type,
                    })
                }
            }
        };

        let (curly, src) = self.unpack_mut();
        curly.lhs = Some(Parsed::new(struct_fqn.clone(), lhs_src));

        let struct_ty = match ctx.tcx.get_struct_ty(&struct_fqn) {
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
            let el_span = ctx.srcmap.span_of(&el);
            let (name, name_span, el) = match el.value {
                ast::CurlyElement::Name(n) => {
                    (n.clone(), el_span, Node::with_id(el.id, Expr::Name(n)))
                }
                ast::CurlyElement::Labeled(n, ex) => (n, el_span, ex),
            };

            let field_name = name.path.name().unwrap();
            if let Some(i) = idx.get(&field_name) {
                param_map.push((*i, name.clone(), el));
            } else {
                return Err(RayError {
                    msg: format!("struct `{}` does not have field `{}`", lhs, name),
                    src: vec![src.respan(name_span)],
                    kind: RayErrorKind::Type,
                });
            }
        }

        param_map.sort_by_key(|(i, ..)| *i);

        let mut elements = vec![];
        for (_, n, el) in param_map.into_iter() {
            let src = ctx.srcmap.get(&el);
            let node = Node::new(ast::CurlyElement::Labeled(n, el));
            ctx.srcmap.set_src(&node, src);
            elements.push(node);
        }

        curly.elements = elements;
        Ok(())
    }
}

impl LowerAST for ast::Dot {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        self.lhs.lower(ctx)
    }
}

impl LowerAST for Sourced<'_, ast::If> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        self.cond.lower(ctx)?;
        self.then.lower(ctx)?;
        self.els.lower(ctx)
    }
}

impl LowerAST for ast::List {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        self.items.lower(ctx)
    }
}

impl LowerAST for Sourced<'_, ast::Name> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::New> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        let (new, src) = self.unpack_mut();
        let scope = &src.path;
        let scopes = ctx.get_scopes(src);
        new.ty.resolve_fqns(scopes, ctx.ncx);
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::Path> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::Pattern> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        let (value, src) = self.unpack_mut();
        match value {
            ast::Pattern::Name(n) | ast::Pattern::Deref(n) => Sourced(n, src).lower(ctx)?,
            ast::Pattern::Sequence(_) => todo!(),
            ast::Pattern::Tuple(_) => todo!(),
        }

        Ok(())
    }
}

impl LowerAST for ast::Range {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        self.start.lower(ctx)?;
        self.end.lower(ctx)
    }
}

impl LowerAST for ast::Sequence {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        self.items.lower(ctx)
    }
}

impl LowerAST for ast::Tuple {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        self.seq.lower(ctx)
    }
}

impl LowerAST for Sourced<'_, ast::UnaryOp> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        let (unop, _) = self.unpack_mut();
        unop.expr.lower(ctx)?;
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::While> {
    type Output = ();

    fn lower(&mut self, ctx: &mut LowerCtx) -> RayResult<Self::Output> {
        self.cond.lower(ctx)?;
        self.body.lower(ctx)
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

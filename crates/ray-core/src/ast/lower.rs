use std::{
    collections::HashMap,
    ops::{Deref, DerefMut},
    vec,
};

use ray_shared::{
    collections::{namecontext::NameContext, nametree::Scope},
    pathlib::{FilePath, Path},
    span::{Source, Sourced, parsed::Parsed},
    ty::{Ty, TyVar},
};
use ray_typing::{constraints::Predicate, tyctx::TyCtx, types::TyScheme};

use crate::{ast::PathBinding, sourcemap::SourceMap};
use crate::{
    ast::{self, Impl},
    errors::{RayError, RayErrorKind, RayResult},
};

use super::{
    Decl, Expr, Extern, Func, FuncSig, Modifier, Node, Struct, Trait, TypeParams,
    expr::{Closure, FnParam, Sequence},
};

fn method_allows_inferred_return(body: &Option<Box<Node<Expr>>>) -> bool {
    let Some(body) = body.as_ref() else {
        return false;
    };

    !matches!(body.value, Expr::Block(_))
}

fn enforce_method_annotation_policy(
    sig: &FuncSig,
    body: &Option<Box<Node<Expr>>>,
    src: &Source,
    srcmap: &SourceMap,
    context: &str,
) -> Result<(), RayError> {
    for (idx, param) in sig.params.iter().enumerate() {
        let is_self = idx == 0 && param.value.name().is_self();
        if is_self {
            continue;
        }

        if param.value.ty().is_none() {
            return Err(RayError {
                msg: format!("parameter `{}` must have a type annotation", param.value),
                src: vec![src.respan(srcmap.span_of(param))],
                kind: RayErrorKind::Type,
                context: Some(context.to_string()),
            });
        }
    }

    if sig.ret_ty.is_none() && !method_allows_inferred_return(body) {
        return Err(RayError {
            msg: str!("method must have a return type annotation unless using `=>`"),
            src: vec![src.respan(sig.span)],
            kind: RayErrorKind::Type,
            context: Some(context.to_string()),
        });
    }

    Ok(())
}

fn annotate_trait_self_param_if_missing(
    sig: &mut FuncSig,
    self_ty: &Ty,
    src: &Source,
    srcmap: &SourceMap,
) {
    let Some(first) = sig.params.first_mut() else {
        return;
    };

    if !first.value.name().is_self() {
        return;
    }

    if first.value.ty().is_some() {
        return;
    }

    let param_src = src.respan(srcmap.span_of(first));
    match &mut first.value {
        FnParam::Name(name) => {
            name.ty = Some(Parsed::new(TyScheme::from_mono(self_ty.clone()), param_src));
        }
        FnParam::Missing { placeholder, .. } => {
            placeholder.ty = Some(Parsed::new(TyScheme::from_mono(self_ty.clone()), param_src));
        }
        FnParam::DefaultValue(_, _) => {}
    }
}

fn map_ty_vars(
    ty_params: Option<&mut TypeParams>,
    scopes: &Vec<Scope>,
    filepath: &FilePath,
    src_module: &Path,
    ncx: &NameContext,
    tcx: &mut TyCtx,
) -> Result<Vec<TyVar>, RayError> {
    let mut ty_vars = vec![];
    if let Some(ty_params) = ty_params {
        for tp in ty_params.tys.iter_mut() {
            tp.resolve_fqns(scopes, ncx);
            tcx.map_vars(tp);
            if let Ty::Var(v) = tp.value() {
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
                    context: Some("get_ty_vars".to_string()),
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

pub struct AstLowerCtx<'a> {
    srcmap: &'a mut SourceMap,
    scope_map: &'a HashMap<Path, Vec<Scope>>,
    tcx: &'a mut TyCtx,
    ncx: &'a mut NameContext,
    identifiers: IdentMap,
    errors: &'a mut Vec<RayError>,
}

impl<'a> AstLowerCtx<'a> {
    pub fn new(
        srcmap: &'a mut SourceMap,
        scope_map: &'a HashMap<Path, Vec<Scope>>,
        tcx: &'a mut TyCtx,
        ncx: &'a mut NameContext,
        errors: &'a mut Vec<RayError>,
    ) -> Self {
        AstLowerCtx {
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
        F: FnOnce(&mut AstLowerCtx) -> A,
    {
        let old_tcx = std::mem::replace(self.tcx, tcx);
        let out = f(self);
        let _ = std::mem::replace(self.tcx, old_tcx);
        out
    }

    pub fn with_clone<F, A>(&mut self, f: F) -> A
    where
        F: FnOnce(&mut AstLowerCtx) -> A,
    {
        let mut ctx = AstLowerCtx {
            srcmap: self.srcmap,
            scope_map: self.scope_map,
            tcx: self.tcx,
            ncx: self.ncx,
            identifiers: self.identifiers.clone(),
            errors: self.errors,
        };
        f(&mut ctx)
    }

    pub fn srcmap(&self) -> &SourceMap {
        &self.srcmap
    }

    #[inline(always)]
    fn get_scopes(&self, src: &Source) -> &Vec<Scope> {
        log::debug!("[get_scopes] src = {:?}", src);
        self.scope_map.get(&src.src_module).unwrap()
    }

    fn resolve_fqn_for_parsed_ty(&self, ty: &mut Parsed<Ty>) {
        let scopes = self.get_scopes(ty.src());
        ty.resolve_fqns(scopes, &self.ncx);
    }
}

pub trait LowerAST
where
    Self: Sized,
{
    type Output;

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output>;
}

impl<T, U> LowerAST for Box<T>
where
    T: LowerAST<Output = U>,
{
    type Output = U;

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<U> {
        self.as_mut().lower(ctx)
    }
}

impl<T, U> LowerAST for Option<T>
where
    T: LowerAST<Output = U>,
{
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<()> {
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

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<()> {
        for t in self.iter_mut() {
            t.lower(ctx)?;
        }
        Ok(())
    }
}

impl LowerAST for Node<Decl> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        let decl = &mut self.value;
        match decl {
            Decl::Mutable(n, _) | Decl::Name(n, _) => {
                if let Some(ty) = n.ty.as_deref_mut() {
                    let scopes = ctx.get_scopes(&src);
                    ty.resolve_fqns(scopes, ctx.ncx);
                }
                // TODO: what do we do here?
                let _ = n.ty.as_deref().unwrap().clone();
            }
            d @ Decl::Declare(_) => unimplemented!("decl to type: {}", d),
            Decl::Func(func) => Sourced(func, &src).lower(ctx)?,
            Decl::FnSig(sig) => todo!("lower: Decl::FnSig: {:?}", sig),
            Decl::Struct(st) => Sourced(st, &src).lower(ctx)?,
            Decl::Trait(tr) => Sourced(tr, &src).lower(ctx)?,
            Decl::TypeAlias(name, ty) => todo!("lower: Decl::TypeAlias: {:?} = {:?}", name, ty),
            Decl::Impl(im) => Sourced(im, &src).lower(ctx)?,
            Decl::FileMain(stmts) => {
                // FileMain statements are lowered separately via build_typecheck_input
                for stmt in stmts {
                    stmt.lower(ctx)?;
                }
            }
        };
        Ok(())
    }
}

impl LowerAST for Sourced<'_, Extern> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<()> {
        let (ext, src) = self.unpack_mut();
        match ext.decl_mut() {
            Decl::Mutable(_, _) => todo!(),
            Decl::Name(_, _) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::FnSig(sig) => {
                let _name = sig
                    .path
                    .name()
                    .ok_or_else(|| RayError {
                        msg: str!("externed function must have a name"),
                        src: vec![src.clone()],
                        kind: RayErrorKind::Type,
                        context: Some("lower extern fn".to_string()),
                    })?
                    .clone();

                // make sure that the signature is fully typed
                let mut fn_tcx = ctx.tcx.clone();
                let scopes = ctx.get_scopes(src);
                sig.resolve_signature(scopes, ctx.ncx)?;
                sig.fresh_scheme(&src.path, &src.filepath, &mut fn_tcx, &ctx.srcmap)?;

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

    fn lower(&mut self, _ctx: &mut AstLowerCtx) -> RayResult<()> {
        unreachable!("legacy code should not be called")

        // let (st, src) = self.unpack_mut();
        // let name = st.path.name().unwrap();
        // let struct_path = if Ty::is_builtin_name(&name) {
        //     Path::from(name)
        // } else {
        //     st.path.value.clone()
        // };

        // let mut struct_tcx = ctx.tcx.clone();
        // let scopes = ctx.get_scopes(src);
        // let ty_vars = map_ty_vars(
        //     st.ty_params.as_mut(),
        //     scopes,
        //     &src.filepath,
        //     &src.src_module,
        //     ctx.ncx,
        //     &mut struct_tcx,
        // )?;

        // let fields = ctx.with_tcx(struct_tcx, |ctx| {
        //     let mut fields = vec![];
        //     if let Some(struct_fields) = &mut st.fields {
        //         for field in struct_fields.iter_mut() {
        //             let ty = if let Some(ty) = &mut field.ty {
        //                 let scopes = ctx.get_scopes(src);
        //                 ty.resolve_fqns(scopes, ctx.ncx);
        //                 ctx.tcx.map_vars(ty.mono_mut());
        //                 ty.clone_value()
        //             } else {
        //                 let src = ctx.srcmap.get(field);
        //                 return Err(RayError {
        //                     msg: format!("struct field on `{}` does not have a type", st.path),
        //                     src: vec![src],
        //                     kind: RayErrorKind::Type,
        //                     context: Some("lower struct field".to_string()),
        //                 });
        //             };

        //             fields.push((field.path.to_string(), ty));
        //         }
        //     }

        //     Ok(fields)
        // })?;

        // let ty = Ty::with_vars(&struct_path, &ty_vars);
        // let struct_ty = TyScheme::new(ty_vars, vec![], ty);
        // ctx.tcx.add_struct_ty(StructTy {
        //     kind: st.kind,
        //     path: struct_path,
        //     ty: struct_ty,
        //     fields,
        // });
        // Ok(())
    }
}

impl LowerAST for Sourced<'_, Trait> {
    type Output = ();

    fn lower(&mut self, _ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        unreachable!("legacy code should not be called")

        // let (tr, src) = self.unpack_mut();
        // let trait_fqn = &src.path;
        // let ty_span = *tr.ty.span().unwrap();
        // let scopes = ctx.get_scopes(src);
        // tr.ty.resolve_fqns(scopes, ctx.ncx);

        // let mut ty_params = match tr.ty.deref() {
        //     Ty::Proj(_, tp) => tp.clone(),
        //     t @ _ => {
        //         return Err(RayError {
        //             msg: format!("expected trait type name with parameters but found `{}`", t),
        //             src: vec![src.respan(ty_span)],
        //             kind: RayErrorKind::Type,
        //             context: Some("lower trait".to_string()),
        //         });
        //     }
        // };

        // let fqn = trait_fqn.to_string();
        // let mut trait_tcx = ctx.tcx.clone();
        // ty_params.iter_mut().for_each(|t| trait_tcx.map_vars(t));

        // if ty_params.is_empty() {
        //     return Err(RayError {
        //         msg: format!("expected a type parameter but found none"),
        //         src: vec![src.respan(ty_span)],
        //         kind: RayErrorKind::Type,
        //         context: Some("lower trait".to_string()),
        //     });
        // }

        // let tp = &ty_params[0];
        // if !matches!(tp, Ty::Var(_)) {
        //     return Err(RayError {
        //         msg: format!("expected a type parameter but found {}", tp),
        //         src: vec![src.respan(ty_span)],
        //         kind: RayErrorKind::Type,
        //         context: Some("lower trait".to_string()),
        //     });
        // }

        // let trait_ty = Ty::with_tys(&fqn, ty_params.clone());

        // let mut fields: Vec<TraitField> = vec![];
        // for func in tr.fields.iter_mut() {
        //     let sig = variant!(func.deref_mut(), if Decl::FnSig(sig));
        //     let func_name = match sig.path.name() {
        //         Some(n) => n,
        //         _ => {
        //             return Err(RayError {
        //                 msg: format!("trait method on `{}` does not have a name", tr.ty),
        //                 src: vec![src.respan(sig.span)],
        //                 kind: RayErrorKind::Type,
        //                 context: Some("lower trait func".to_string()),
        //             });
        //         }
        //     };

        //     let mut fn_tcx = trait_tcx.clone();
        //     let scopes = ctx.get_scopes(src);
        //     sig.resolve_signature(scopes, ctx.ncx)?;

        //     // Trait methods follow the same "no unannotated methods" policy as impl
        //     // methods, except that `self` may omit a type annotation. For trait
        //     // declarations, an unannotated `self` defaults to the trait's first
        //     // type parameter (the receiver).
        //     annotate_trait_self_param_if_missing(sig, tp, src, &ctx.srcmap);
        //     enforce_method_annotation_policy(sig, &None, src, &ctx.srcmap, "lower trait func")?;

        //     sig.fresh_scheme(trait_fqn, &src.filepath, &mut fn_tcx, &ctx.srcmap)?;

        //     // add the trait type to the qualifiers
        //     let scheme = sig.ty.as_mut().unwrap();
        //     scheme.qualifiers_mut().insert(
        //         0,
        //         Predicate::class(trait_fqn.without_type_args().to_string(), ty_params.clone()),
        //     );

        //     log::debug!("trait func scheme = {:?}", scheme);

        //     // Borrow the function type to inspect its parameters, but immediately
        //     // clone the parameter list so we can later mutate the scheme safely.
        //     let param_tys = match scheme.mono().try_borrow_fn() {
        //         Ok((p, _)) => p,
        //         Err(err) => return Err(TypeError::message(err, TypeSystemInfo::new()).into()),
        //     };
        //     let param_tys = param_tys.clone();
        //     let func_fqn = trait_fqn
        //         .append_type_args(ty_params.iter())
        //         .append(&func_name);
        //     log::debug!("add fqn: {} => {}", func_name, func_fqn);

        //     if param_tys.len() == 2 && ast::InfixOp::is(&func_name) {
        //         ctx.tcx
        //             .add_infix_op(func_name.clone(), func_fqn.clone(), trait_fqn.clone());
        //     } else if param_tys.len() == 1 && ast::PrefixOp::is(&func_name) {
        //         ctx.tcx
        //             .add_prefix_op(func_name.clone(), func_fqn.clone(), trait_fqn.clone());
        //     } else {
        //         log::debug!("add name in scope: {} => {}", func_name, trait_fqn);
        //         let scope = trait_fqn.to_name_vec();
        //         ctx.ncx
        //             .nametree_mut()
        //             .add_name_in_scope(&scope, func_name.clone())
        //     }

        //     // Determine whether this method is static. Non-static methods are
        //     // considered receiver methods at the call site, but we no longer
        //     // bake any Recv predicates into their type schemes here.
        //     let is_static = sig
        //         .modifiers
        //         .iter()
        //         .any(|m| matches!(m, ast::Modifier::Static));

        //     let recv_mode = ReceiverMode::from_signature(&param_tys, is_static);

        //     fields.push(TraitField {
        //         kind: FieldKind::Method,
        //         name: func_name.clone(),
        //         ty: scheme.clone(),
        //         recv_mode,
        //         is_static,
        //     });

        //     sig.path.value = func_fqn;
        // }

        // let scopes = ctx.get_scopes(src);
        // let super_trait = if let Some(ty) = &tr.super_trait {
        //     let (mut ty, src, _) = ty.clone().take();
        //     if !matches!(ty, Ty::Proj(_, _)) {
        //         return Err(RayError {
        //             msg: format!("expected super trait of form T[..], but found {}", ty),
        //             src: vec![src],
        //             kind: RayErrorKind::Type,
        //             context: Some("lower trait".to_string()),
        //         });
        //     }

        //     ty.resolve_fqns(scopes, ctx.ncx);
        //     Some(ty)
        // } else {
        //     None
        // };

        // let default_ty = tr
        //     .directives
        //     .iter()
        //     .find_map(|directive| match directive.kind {
        //         TraitDirectiveKind::Default => {
        //             directive.args.first().map(|arg| arg.value().clone())
        //         }
        //     });

        // let fqn = trait_fqn.to_name_vec();
        // ctx.ncx.nametree_mut().add_full_name(&fqn);
        // ctx.tcx.add_trait_ty(TraitTy {
        //     path: trait_fqn.clone(),
        //     ty: trait_ty,
        //     super_traits: super_trait.map(|s| vec![s]).unwrap_or_default(),
        //     fields,
        //     default_ty,
        // });

        // Ok(())
    }
}

impl LowerAST for Sourced<'_, Impl> {
    type Output = ();

    fn lower(&mut self, _ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        unreachable!("legacy code should not be called")

        // let (imp, src) = self.unpack_mut();
        // ctx.resolve_fqn_for_parsed_ty(&mut imp.ty);

        // let (trait_fqn, orig_ty_args) = match imp.ty.deref() {
        //     Ty::Proj(path, ty_params) => (path, ty_params.clone()),
        //     t => {
        //         return Err(RayError {
        //             msg: format!(
        //                 "`{}` is not a valid {}",
        //                 t,
        //                 if imp.is_object { "object" } else { "trait" }
        //             ),
        //             src: vec![src.respan(*imp.ty.span().unwrap())],
        //             kind: RayErrorKind::Type,
        //             context: Some("lower trait impl".to_string()),
        //         });
        //     }
        // };

        // // lookup the trait in the context
        // log::debug!("found fqn: {}", trait_fqn);
        // let trait_ty = if !imp.is_object {
        //     match ctx.tcx.get_trait_ty(&trait_fqn) {
        //         Some(t) => Some(t.clone()),
        //         _ => {
        //             return Err(RayError {
        //                 msg: format!("trait `{}` is not defined", trait_fqn),
        //                 src: vec![src.respan(*imp.ty.span().unwrap())],
        //                 kind: RayErrorKind::Type,
        //                 context: Some("lower trait impl".to_string()),
        //             });
        //         }
        //     }
        // } else {
        //     None
        // };

        // // get the type parameter of the original trait
        // let mut trait_ty_params = vec![];
        // if let Some(trait_ty) = &trait_ty {
        //     let orig_trait_tps = trait_ty.ty.type_arguments();
        //     for ty in orig_trait_tps {
        //         let Ty::Var(v) = ty else {
        //             return Err(RayError {
        //                 msg: str!("expected a type parameter for trait"),
        //                 src: vec![src.respan(*imp.ty.span().unwrap())],
        //                 kind: RayErrorKind::Type,
        //                 context: Some("lower trait impl".to_string()),
        //             });
        //         };

        //         trait_ty_params.push(v.clone());
        //     }
        // }

        // let impl_scope = if imp.is_object {
        //     imp.ty.get_path()
        // } else {
        //     orig_ty_args[0].get_path()
        // };
        // log::debug!("impl fqn: {}", impl_scope);
        // let mut impl_tcx = ctx.tcx.clone();
        // let mut impl_set = HashMap::new();
        // let mut impl_srcs = HashMap::new();

        // let mut ty_args = orig_ty_args.clone();
        // ty_args.iter_mut().for_each(|t| impl_tcx.map_vars(t));

        // let mut trait_arg_subst = Subst::new();
        // for (ty_param, ty_arg) in trait_ty_params.iter().zip(&ty_args) {
        //     trait_arg_subst.insert(ty_param.clone(), ty_arg.clone());
        // }

        // // resolve any qualifiers
        // for qualifier in &mut imp.qualifiers {
        //     ctx.resolve_fqn_for_parsed_ty(qualifier);
        // }
        // let impl_qualifiers = imp.qualifiers.clone();

        // // consts have to be first in case they're used inside of functions
        // if let Some(consts) = &mut imp.consts {
        //     for const_node in consts {
        //         const_node.lower(ctx)?;
        //         let path = const_node.lhs.path_mut().unwrap();
        //         let name = path.name().unwrap();
        //         *path = impl_scope.append(&name);
        //         ctx.ncx.nametree_mut().add_full_name(&path.to_name_vec());
        //     }
        // }

        // let mut fields = vec![];
        // if let Some(funcs) = &mut imp.funcs {
        //     for func in funcs {
        //         func.sig.qualifiers.extend(impl_qualifiers.iter().cloned());

        //         let func_name = match func.sig.path.name() {
        //             Some(n) => n,
        //             _ => {
        //                 return Err(RayError {
        //                     msg: format!("trait function on `{}` does not have a name", trait_fqn),
        //                     src: vec![src.respan(func.sig.span)],
        //                     kind: RayErrorKind::Type,
        //                     context: Some("lower trait func".to_string()),
        //                 });
        //             }
        //         };

        //         // make this a fully-qualified name
        //         func.sig.path.value = if imp.is_object {
        //             trait_fqn.append(&func_name)
        //         } else {
        //             trait_fqn
        //                 .append_type_args(ty_args.iter())
        //                 .append(&func_name)
        //         };
        //         log::debug!("func fqn: {}", func.sig.path);
        //         ctx.ncx
        //             .nametree_mut()
        //             .add_full_name(&func.sig.path.to_name_vec());

        //         enforce_method_annotation_policy(
        //             &func.sig,
        //             &func.body,
        //             src,
        //             &ctx.srcmap,
        //             "lower trait impl",
        //         )?;

        //         if let Some(field) = trait_ty.as_ref().and_then(|tr| tr.get_field(&func_name)) {
        //             let mut scheme = field.ty.clone();
        //             scheme.apply_subst(&trait_arg_subst);

        //             if let Some(self_ty) = scheme
        //                 .ty
        //                 .try_borrow_fn()
        //                 .ok()
        //                 .and_then(|(params, _)| params.first())
        //             {
        //                 annotate_trait_self_param_if_missing(
        //                     &mut func.sig,
        //                     self_ty,
        //                     src,
        //                     &ctx.srcmap,
        //                 );
        //             }
        //         }

        //         let src = ctx.srcmap.get(&func);
        //         let fn_tcx = impl_tcx.clone();
        //         ctx.with_tcx(fn_tcx, |ctx| Sourced(&mut func.value, &src).lower(ctx))?;

        //         let func_src = ctx.srcmap.get(func);
        //         let sig_src = func_src.respan(func.sig.span);
        //         let is_static = func
        //             .sig
        //             .modifiers
        //             .iter()
        //             .any(|m| matches!(m, ast::Modifier::Static));

        //         let param_tys = func
        //             .sig
        //             .ty
        //             .as_ref()
        //             .and_then(|ty| ty.try_borrow_fn())
        //             .map(|(_, _, params, _)| &params[..])
        //             .expect("parameter types for impl method");

        //         let recv_mode = ReceiverMode::from_signature(&param_tys, is_static);
        //         log::debug!(
        //             "[Impl::lower] sig.path = {}, param_tys = [{}], is_static = {}, recv_mode = {:?}",
        //             func.sig.path.value,
        //             join(param_tys, ", "),
        //             is_static,
        //             recv_mode
        //         );
        //         if imp.is_object {
        //             fields.push(ImplField {
        //                 kind: FieldKind::Method,
        //                 path: func.sig.path.value.clone(),
        //                 scheme: func.sig.ty.clone(),
        //                 src: sig_src,
        //                 recv_mode,
        //                 is_static,
        //             });
        //         } else {
        //             impl_srcs.insert(func_name.clone(), sig_src);
        //             impl_set.insert(
        //                 func_name,
        //                 Some((
        //                     func.sig.path.value.clone(),
        //                     func.sig.ty.clone(),
        //                     recv_mode,
        //                     is_static,
        //                 )),
        //             );
        //         }
        //     }
        // }

        // if let Some(ext) = &mut imp.externs {
        //     for e in ext {
        //         let name = e.get_name().unwrap();
        //         let src = ctx.srcmap.get(e);
        //         impl_srcs.insert(name.clone(), src);
        //         impl_set.insert(name, None);
        //         e.lower(ctx)?;
        //     }
        // }

        // // make sure that everything has been implemented
        // if let Some(trait_ty) = &trait_ty {
        //     for field in trait_ty.fields.iter() {
        //         let n = &field.name;
        //         let Some(def) = impl_set.get(n) else {
        //             return Err(RayError {
        //                 msg: format!("trait implementation is missing for field `{}`", n),
        //                 src: vec![src.respan(*imp.ty.span().unwrap())],
        //                 kind: RayErrorKind::Type,
        //                 context: Some("lower trait impl".to_string()),
        //             });
        //         };

        //         if let Some((path, scheme, recv_mode, is_static)) = def {
        //             log::debug!("[Impl::lower] field path={}, scheme={:?}", path, scheme);
        //             let src = impl_srcs.get(n).cloned().unwrap_or_else(|| src.clone());
        //             fields.push(ImplField {
        //                 kind: field.kind,
        //                 path: path.clone(),
        //                 scheme: scheme.clone(),
        //                 src,
        //                 recv_mode: *recv_mode,
        //                 is_static: *is_static,
        //             });
        //         }
        //     }
        // }

        // if !imp.is_object && trait_ty_params.len() != ty_args.len() {
        //     return Err(RayError {
        //         msg: format!(
        //             "trait expected {} type argument(s) but found {}",
        //             trait_ty_params.len(),
        //             ty_args.len()
        //         ),
        //         src: vec![src.respan(*imp.ty.span().unwrap())],
        //         kind: RayErrorKind::Type,
        //         context: Some("lower trait impl".to_string()),
        //     });
        // }

        // let mut predicates = vec![];
        // for q in imp.qualifiers.iter() {
        //     predicates.push(predicate_from_ast_ty(
        //         &q,
        //         &impl_scope,
        //         &src.filepath,
        //         &mut impl_tcx,
        //     )?);
        // }

        // let kind = if let Some(trait_ty) = &trait_ty {
        //     let mut trait_ty = trait_ty.ty.clone();
        //     trait_ty.apply_subst(&trait_arg_subst);
        //     let base_ty = ty_args[0].clone();

        //     ImplKind::Trait {
        //         base_ty,
        //         trait_ty,
        //         ty_args: ty_args[1..].to_vec(),
        //     }
        // } else {
        //     let mut recv_ty = imp.ty.deref().clone();
        //     impl_tcx.map_vars(&mut recv_ty);
        //     ImplKind::Inherent { recv_ty }
        // };

        // let impl_ty = ImplTy {
        //     kind,
        //     predicates,
        //     fields,
        // };
        // ctx.tcx.add_impl(trait_fqn.clone(), impl_ty);
        // Ok(())
    }
}

impl LowerAST for Sourced<'_, Func> {
    type Output = ();

    fn lower<'a>(&mut self, ctx: &mut AstLowerCtx<'a>) -> RayResult<()> {
        let (func, src) = self.unpack_mut();
        if func.sig.is_anon {
            return Err(RayError {
                msg: format!("top-level function must have a name"),
                src: vec![src.clone()],
                kind: RayErrorKind::Name,
                context: Some("lower func".to_string()),
            });
        }

        if !func.sig.is_method {
            log::debug!("add fqn: {}", func.sig.path);
            ctx.ncx
                .nametree_mut()
                .add_full_name(&func.sig.path.to_name_vec());
        }

        let mut fn_tcx = ctx.tcx.clone();
        if func.sig.ty.is_none() {
            let num_typed = func.sig.params.iter().filter(|p| p.ty().is_some()).count();
            let mut expected = func.sig.params.len();

            if func.sig.is_method {
                if let Some(first) = func.sig.params.first() {
                    if first.value.name().is_self() && first.value.ty().is_none() {
                        expected = expected.saturating_sub(1);
                    }
                }
            }

            if num_typed != 0 && num_typed != expected {
                return Err(RayError {
                    msg: format!("cannot infer type of only some parameters"),
                    src: vec![src.clone()],
                    kind: RayErrorKind::Type,
                    context: Some("lower func".to_string()),
                });
            }
        }

        let fn_scope = func.sig.path.clone();
        let scopes = ctx.get_scopes(src);
        func.sig.resolve_signature(scopes, &ctx.ncx)?;

        let num_typed = func.sig.params.iter().filter(|p| p.ty().is_some()).count();
        if num_typed == func.sig.params.len() {
            func.sig
                .fresh_scheme(&fn_scope, &src.filepath, &mut fn_tcx, &ctx.srcmap)?;
        }

        ctx.with_tcx(fn_tcx, |ctx| func.body.lower(ctx))
    }
}

impl LowerAST for Node<Expr> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        match &mut self.value {
            Expr::Assign(assign) => assign.lower(ctx),
            Expr::BinOp(b) => Sourced(b, &src).lower(ctx),
            Expr::Block(b) => b.lower(ctx),
            Expr::Boxed(b) => b.inner.lower(ctx),
            Expr::Break(value) => {
                if let Some(value) = value {
                    value.lower(ctx)?;
                }
                Ok(())
            }
            Expr::Continue => Ok(()),
            Expr::Call(c) => c.lower(ctx),
            Expr::Cast(c) => Sourced(c, &src).lower(ctx),
            Expr::Closure(closure) => closure.lower(ctx),
            Expr::Curly(c) => Sourced(c, &src).lower(ctx),
            Expr::Dict(dict) => {
                for (key, value) in dict.entries.iter_mut() {
                    key.lower(ctx)?;
                    value.lower(ctx)?;
                }
                Ok(())
            }
            Expr::DefaultValue(_) => todo!("lower: Expr::DefaultValue: {:?}", self),
            Expr::Deref(d) => d.expr.lower(ctx),
            Expr::Dot(d) => d.lower(ctx),
            Expr::Func(func) => {
                let mut closure = func_literal_to_closure(func, &src)?;
                closure.lower(ctx)?;
                self.value = Expr::Closure(closure);
                Ok(())
            }
            Expr::For(for_loop) => {
                let pat_src = ctx.srcmap.get(&for_loop.pat);
                Sourced(&mut for_loop.pat.value, &pat_src).lower(ctx)?;
                for_loop.expr.lower(ctx)?;
                for_loop.body.lower(ctx)
            }
            Expr::If(if_ex) => Sourced(if_ex, &src).lower(ctx),
            Expr::Index(index) => {
                index.index.lower(ctx)?;
                index.lhs.lower(ctx)?;
                Ok(())
            }
            Expr::Labeled(_, _) => todo!("lower: Expr::Labeled: {:?}", self),
            Expr::List(l) => l.lower(ctx),
            Expr::Literal(_) => Ok(()),
            Expr::Loop(_) => Ok(()),
            Expr::Name(n) => Sourced(n, &src).lower(ctx),
            Expr::New(n) => Sourced(n, &src).lower(ctx),
            Expr::Pattern(p) => Sourced(p, &src).lower(ctx),
            Expr::Path(_) => Ok(()), // Path segments are strings, no lowering needed
            Expr::Paren(ex) => ex.lower(ctx),
            Expr::Range(r) => r.lower(ctx),
            Expr::Ref(r) => r.lower(ctx),
            Expr::Return(r) => {
                if let Some(expr) = r {
                    expr.lower(ctx)?;
                }
                Ok(())
            }
            Expr::Sequence(seq) => seq.lower(ctx),
            Expr::Set(set) => {
                for item in set.items.iter_mut() {
                    item.lower(ctx)?;
                }
                Ok(())
            }
            Expr::ScopedAccess(scoped_access) => {
                scoped_access.lhs.lower(ctx)?;
                Sourced(&mut scoped_access.rhs.value, &src).lower(ctx)
            }
            Expr::Tuple(t) => t.lower(ctx),
            Expr::Type(ty) => Sourced(ty, &src).lower(ctx),
            Expr::TypeAnnotated(_, _) => {
                todo!()
            }
            Expr::UnaryOp(u) => Sourced(u, &src).lower(ctx),
            Expr::Unsafe(_) => todo!("lower: Expr::Unsafe: {:?}", self),
            Expr::While(w) => Sourced(w, &src).lower(ctx),
            Expr::Missing(_) => todo!("lower: Expr::Missing: {:?}", self),
            Expr::Some(expr) => expr.lower(ctx),
        }
    }
}

impl LowerAST for Closure {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<()> {
        for arg in self.args.items.iter_mut() {
            arg.lower(ctx)?;
        }
        self.body.lower(ctx)
    }
}

impl LowerAST for ast::Assign {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<()> {
        // check each identifier for mutability
        for node in self.lhs.paths() {
            let PathBinding { path, is_bindable } = node.value;
            match ctx.identifiers.get(path) {
                Some(ident) if !ident.is_mut && ident.in_current_scope => {
                    let src = ctx.srcmap.get(&node);
                    ctx.errors.push(RayError {
                        msg: format!("cannot assign to immutable identifier `{}`", path),
                        src: vec![src],
                        kind: RayErrorKind::Type,
                        context: Some("lower assignment".to_string()),
                    });
                }
                Some(_) if !is_bindable => { /* do nothing */ }
                _ => {
                    ctx.identifiers.insert(
                        path.clone(),
                        Ident {
                            is_mut: self.is_mut,
                            in_current_scope: true,
                        },
                    );
                }
            }
        }

        log::debug!("[Assign::lower] op = {:?}", self.op);

        if let ast::InfixOp::AssignOp(op) = &mut self.op {
            let lhs_src = ctx.srcmap.get(&self.lhs);
            let mut lhs: Node<Expr> = match self.lhs.clone().try_take_map(|pat| match pat {
                ast::Pattern::Name(_) | ast::Pattern::Dot(_, _) | ast::Pattern::Index(_, _, _) => {
                    Ok(pat.into())
                }
                ast::Pattern::Sequence(_)
                | ast::Pattern::Tuple(_)
                | ast::Pattern::Deref(_)
                | ast::Pattern::Some(_)
                | ast::Pattern::Missing(_) => Err(RayError {
                    msg: str!("cannot use expression as l-value for re-assignment"),
                    src: vec![lhs_src],
                    kind: RayErrorKind::Type,
                    context: Some("lower assignment".to_string()),
                }),
            }) {
                Ok(lhs) => lhs,
                Err(err) => {
                    ctx.errors.push(err);
                    return Ok(());
                }
            };

            log::debug!("[Assign::lower] lower lhs = {}", lhs);
            lhs.lower(ctx)?;

            let new_op = Node::new(ast::InfixOp::Assign);
            let op_src = ctx.srcmap.get(op);
            ctx.srcmap.set_src(&new_op, op_src);

            let op = std::mem::replace(op.as_mut(), new_op);

            let mut old_rhs = self.rhs.clone();
            old_rhs.lower(ctx)?;

            let lhs_src = ctx.srcmap.get(&lhs);
            let rhs_src = ctx.srcmap.get(&old_rhs);
            let src = lhs_src.extend_to(&rhs_src);
            let node = Node::new(Expr::BinOp(ast::BinOp {
                lhs: Box::new(lhs),
                rhs: old_rhs,
                op,
            }));
            ctx.srcmap.set_src(&node, src);

            self.rhs = Box::new(node);
        } else {
            let lhs_src = ctx.srcmap.get(&self.lhs);
            Sourced(&mut self.lhs.value, &lhs_src).lower(ctx)?;

            self.rhs.lower(ctx)?;
        };

        if matches!(self.op, ast::InfixOp::AssignOp(_)) {
            self.op = ast::InfixOp::Assign;
        }

        Ok(())
    }
}

fn func_literal_to_closure(func: &mut Func, src: &Source) -> RayResult<Closure> {
    if !func.sig.is_anon {
        return Err(RayError {
            msg: "function literals must be anonymous".to_string(),
            src: vec![src.clone()],
            kind: RayErrorKind::Parse,
            context: Some("lower inline function literal".to_string()),
        });
    }
    if func.sig.ty_params.is_some() {
        return Err(RayError {
            msg: "function literals cannot declare type parameters yet".to_string(),
            src: vec![src.clone()],
            kind: RayErrorKind::Parse,
            context: Some("lower inline function literal".to_string()),
        });
    }
    if !func.sig.qualifiers.is_empty() {
        return Err(RayError {
            msg: "function literals cannot declare where-clauses yet".to_string(),
            src: vec![src.clone()],
            kind: RayErrorKind::Parse,
            context: Some("lower inline function literal".to_string()),
        });
    }
    let body = func.body.take().ok_or_else(|| RayError {
        msg: "function literal is missing a body".to_string(),
        src: vec![src.clone()],
        kind: RayErrorKind::Parse,
        context: Some("lower inline function literal".to_string()),
    })?;

    let mut params = Vec::with_capacity(func.sig.params.len());
    for param in &func.sig.params {
        match &param.value {
            FnParam::Name(name) => {
                params.push(Node::with_id(param.id, Expr::Name(name.clone())));
            }
            _ => {
                return Err(RayError {
                    msg: "function literal parameters must be simple names".to_string(),
                    src: vec![src.clone()],
                    kind: RayErrorKind::Parse,
                    context: Some("lower inline function literal".to_string()),
                });
            }
        }
    }

    Ok(Closure {
        args: Sequence::new(params),
        body,
        arrow_span: None,
        curly_spans: None,
    })
}

impl LowerAST for Sourced<'_, ast::BinOp> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        let (binop, _) = self.unpack_mut();
        binop.lhs.lower(ctx)?;
        binop.rhs.lower(ctx)?;
        Ok(())
    }
}

impl LowerAST for ast::Block {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        ctx.with_clone(|ctx| self.stmts.lower(ctx))
    }
}

impl LowerAST for ast::Call {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        self.callee.lower(ctx)?;
        self.args.items.lower(ctx)
    }
}

impl LowerAST for Sourced<'_, ast::Cast> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        let (cast, src) = self.unpack_mut();
        cast.lhs.lower(ctx)?;
        let scopes = ctx.get_scopes(src);
        cast.ty.resolve_fqns(scopes, ctx.ncx);
        ctx.tcx.map_vars(&mut cast.ty);
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::Curly> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        unreachable!("DO NOT REMOVE THIS PANIC: legacy code should not be called")

        // if self.lhs.is_none() {
        //     unimplemented!("anon struct construction: {}", self.value())
        // }

        // let (curly, src) = self.unpack();
        // let (lhs, lhs_src, _) = curly.lhs.as_ref().unwrap().clone().take();
        // let lhs_span = lhs_src.span.unwrap();
        // let scopes = ctx.scope_map.get(self.src_module()).unwrap();
        // let name = lhs.name().unwrap();
        // let struct_fqn = if Ty::is_builtin_name(&name) {
        //     Path::from(name)
        // } else {
        //     match ctx.ncx.resolve_name(scopes, &name) {
        //         Some(fqn) => fqn.clone(),
        //         _ => {
        //             return Err(RayError {
        //                 msg: format!("struct type `{}` is undefined", lhs),
        //                 src: vec![src.respan(lhs_span)],
        //                 kind: RayErrorKind::Type,
        //                 context: Some("lower curly struct".to_string()),
        //             });
        //         }
        //     }
        // };

        // let (curly, src) = self.unpack_mut();
        // curly.lhs = Some(Parsed::new(struct_fqn.clone(), lhs_src));

        // let struct_ty = match ctx.tcx.get_struct_ty(&ItemPath::from(&struct_fqn)) {
        //     Some(t) => t,
        //     _ => {
        //         return Err(RayError {
        //             msg: format!("struct type `{}` is undefined", lhs),
        //             src: vec![src.respan(lhs_span)],
        //             kind: RayErrorKind::Type,
        //             context: Some("lower curly struct".to_string()),
        //         });
        //     }
        // };

        // curly.ty = struct_ty.ty.clone();
        // log::debug!("lower Curly: set ty for {:?} to {}", struct_fqn, curly.ty);

        // let mut idx = HashMap::new();
        // for (i, (f, _)) in struct_ty.fields.iter().enumerate() {
        //     idx.insert(f.clone(), i);
        // }

        // let mut param_map = vec![];
        // for el in curly.elements.drain(..) {
        //     let el_span = ctx.srcmap.span_of(&el);
        //     let (name, name_span, el) = match el.value {
        //         ast::CurlyElement::Name(n) => {
        //             (n.clone(), el_span, Node::with_id(el.id, Expr::Name(n)))
        //         }
        //         ast::CurlyElement::Labeled(n, mut ex) => {
        //             ex.lower(ctx)?;
        //             (n, el_span, ex)
        //         }
        //     };

        //     let field_name = name.path.name().unwrap();
        //     if let Some(i) = idx.get(&field_name) {
        //         param_map.push((*i, name.clone(), el));
        //     } else {
        //         return Err(RayError {
        //             msg: format!("struct `{}` does not have field `{}`", lhs, name),
        //             src: vec![src.respan(name_span)],
        //             kind: RayErrorKind::Type,
        //             context: Some("lower curly struct".to_string()),
        //         });
        //     }
        // }

        // param_map.sort_by_key(|(i, ..)| *i);

        // let mut elements = vec![];
        // for (_, n, el) in param_map.into_iter() {
        //     let src = ctx.srcmap.get(&el);
        //     let node = Node::new(ast::CurlyElement::Labeled(n, el));
        //     ctx.srcmap.set_src(&node, src);
        //     ctx.srcmap.mark_synthetic(node.id);
        //     elements.push(node);
        // }

        // curly.elements = elements;
        // Ok(())
    }
}

impl LowerAST for ast::Dot {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        self.lhs.lower(ctx)
    }
}

impl LowerAST for Sourced<'_, ast::If> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        self.cond.lower(ctx)?;
        self.then.lower(ctx)?;
        self.els.lower(ctx)
    }
}

impl LowerAST for ast::List {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        self.items.lower(ctx)
    }
}

impl LowerAST for Sourced<'_, ast::Name> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        let (name, src) = self.unpack_mut();
        let scopes = ctx.get_scopes(src);
        if let Some(ty) = &mut name.ty {
            log::debug!("[Name::lower] resolve FQN for scheme (before): {}", ty);
            ty.resolve_fqns(scopes, ctx.ncx);
            log::debug!("[Name::lower] resolve FQN for scheme (after): {}", ty);
        }
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::New> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        let (new, src) = self.unpack_mut();
        let scopes = ctx.get_scopes(src);
        new.ty.resolve_fqns(scopes, ctx.ncx);
        Ok(())
    }
}

impl LowerAST for Sourced<'_, Path> {
    type Output = ();

    fn lower(&mut self, _: &mut AstLowerCtx) -> RayResult<Self::Output> {
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::Pattern> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        let (value, src) = self.unpack_mut();
        match value {
            ast::Pattern::Name(n) | ast::Pattern::Deref(Node { id: _, value: n }) => {
                Sourced(n, src).lower(ctx)?
            }
            ast::Pattern::Dot(lhs, rhs) => {
                let lhs_src = ctx.srcmap.get(lhs);
                Sourced(&mut lhs.as_mut().value, &lhs_src).lower(ctx)?;
                let rhs_src = ctx.srcmap.get(rhs);
                Sourced(&mut rhs.value, &rhs_src).lower(ctx)?;
            }
            ast::Pattern::Index(lhs, index, _) => {
                let lhs_src = ctx.srcmap.get(lhs.as_ref());
                Sourced(&mut lhs.as_mut().value, &lhs_src).lower(ctx)?;
                index.lower(ctx)?;
            }
            ast::Pattern::Some(inner) => {
                let inner_src = ctx.srcmap.get(inner.as_ref());
                Sourced(&mut inner.as_mut().value, &inner_src).lower(ctx)?;
            }
            ast::Pattern::Sequence(pats) | ast::Pattern::Tuple(pats) => {
                for pat in pats {
                    let pat_src = ctx.srcmap.get(pat);
                    Sourced(&mut pat.value, &pat_src).lower(ctx)?;
                }
            }
            ast::Pattern::Missing(_) => {}
        }

        Ok(())
    }
}

impl LowerAST for ast::Range {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        self.start.lower(ctx)?;
        self.end.lower(ctx)
    }
}

impl LowerAST for ast::Ref {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        self.expr.lower(ctx)
    }
}

impl LowerAST for ast::Sequence {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        self.items.lower(ctx)
    }
}

impl LowerAST for ast::Tuple {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        self.seq.lower(ctx)
    }
}

impl LowerAST for Sourced<'_, Parsed<TyScheme>> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        let (ty_scheme, src) = self.unpack_mut();
        let scopes = ctx.get_scopes(&src);
        ty_scheme.mono_mut().resolve_fqns(scopes, ctx.ncx);
        // Normalize type variables (e.g. `'k`) into the same internal tyvar
        // namespace used by signature schemes so expression-level type
        // applications like `T['a]::method` unify correctly.
        ctx.tcx.map_vars(ty_scheme.mono_mut());
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::UnaryOp> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        let (unop, _) = self.unpack_mut();
        unop.expr.lower(ctx)?;
        Ok(())
    }
}

impl LowerAST for Sourced<'_, ast::While> {
    type Output = ();

    fn lower(&mut self, ctx: &mut AstLowerCtx) -> RayResult<Self::Output> {
        self.cond.lower(ctx)?;
        self.body.lower(ctx)
    }
}

pub fn predicate_from_ast_ty(
    _q: &Parsed<Ty>,
    _scope: &Path,
    _filepath: &FilePath,
    _tcx: &mut TyCtx,
) -> Result<Predicate, RayError> {
    unreachable!("legacy code should not be called")

    // // resolve the type
    // let ty_span = *q.span().unwrap();
    // let q = q.clone_value();
    // let (fqn, mut ty_args) = match q {
    //     Ty::Proj(path, args) => (path, args),
    //     _ => {
    //         return Err(RayError {
    //             msg: str!("qualifier must be a trait type"),
    //             src: vec![Source {
    //                 span: Some(ty_span),
    //                 filepath: filepath.clone(),
    //                 path: scope.clone(),
    //                 ..Default::default()
    //             }],
    //             kind: RayErrorKind::Type,
    //             context: Some("lower predicate".to_string()),
    //         });
    //     }
    // };

    // for ty_arg in ty_args.iter_mut() {
    //     tcx.map_vars(ty_arg);
    // }

    // log::debug!("converting from ast type: {}", fqn);
    // let trait_ty = match tcx.get_trait_ty(&fqn) {
    //     Some(t) => t,
    //     _ => {
    //         return Err(RayError {
    //             msg: format!("trait `{}` is not defined", fqn),
    //             src: vec![Source {
    //                 span: Some(ty_span),
    //                 filepath: filepath.clone(),
    //                 ..Default::default()
    //             }],
    //             kind: RayErrorKind::Type,
    //             context: Some("lower predicate".to_string()),
    //         });
    //     }
    // };

    // let mut trait_ty = trait_ty.ty.clone();
    // let ty_param_vars = trait_ty
    //     .type_arguments()
    //     .iter()
    //     .map(|ty| variant!(ty, if Ty::Var(v)))
    //     .cloned()
    //     .collect::<Vec<_>>();

    // let mut sub = Subst::new();
    // for (v, t) in ty_param_vars.iter().zip(ty_args.iter()) {
    //     sub.insert(v.clone(), t.clone());
    // }

    // trait_ty.apply_subst(&sub);

    // let fqn = trait_ty.get_path().without_type_args();
    // Ok(Predicate::class(fqn.to_string(), ty_args))
}

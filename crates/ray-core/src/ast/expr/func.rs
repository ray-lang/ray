use std::ops::{Deref as _, DerefMut as _};

use ray_shared::{
    collections::{namecontext::NameContext, nametree::Scope},
    def::SignatureStatus,
    pathlib::{FilePath, Path},
    span::{Span, parsed::Parsed},
    ty::{Ty, TyVar},
};
use ray_typing::{
    constraints::Predicate,
    tyctx::TyCtx,
    types::{Subst, Substitutable, TyScheme},
};

use crate::sourcemap::SourceMap;
use crate::{
    ast::{Expr, Missing, Modifier, Name, Node, TypeParams},
    errors::RayError,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FnParam {
    Name(Name),
    DefaultValue(Box<Node<FnParam>>, Box<Node<Expr>>),
    Missing { info: Missing, placeholder: Name },
}

impl std::fmt::Display for FnParam {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FnParam::Name(n) => write!(f, "{}", n),
            FnParam::DefaultValue(p, v) => write!(f, "{} = {}", p, v),
            FnParam::Missing { info, .. } => write!(f, "(missing {})", info),
        }
    }
}

impl FnParam {
    pub fn name(&self) -> &Path {
        match self {
            FnParam::DefaultValue(p, _) => p.name(),
            FnParam::Name(n) => &n.path,
            FnParam::Missing { placeholder, .. } => &placeholder.path,
        }
    }

    pub fn name_mut(&mut self) -> &mut Path {
        match self {
            FnParam::DefaultValue(p, _) => p.name_mut(),
            FnParam::Name(n) => &mut n.path,
            FnParam::Missing { placeholder, .. } => &mut placeholder.path,
        }
    }

    pub fn parsed_ty(&self) -> Option<&Parsed<TyScheme>> {
        match self {
            FnParam::DefaultValue(p, _) => p.parsed_ty(),
            FnParam::Name(n) => n.ty.as_ref(),
            FnParam::Missing { placeholder, .. } => placeholder.ty.as_ref(),
        }
    }

    pub fn ty(&self) -> Option<&Ty> {
        match self {
            FnParam::DefaultValue(p, _) => p.ty(),
            FnParam::Name(n) => n.ty.as_deref().map(|t| t.mono()),
            FnParam::Missing { placeholder, .. } => placeholder.ty.as_deref().map(|t| t.mono()),
        }
    }

    pub fn ty_mut(&mut self) -> Option<&mut Ty> {
        match self {
            FnParam::DefaultValue(p, _) => p.ty_mut(),
            FnParam::Name(n) => n.ty.as_deref_mut().map(|t| t.mono_mut()),
            FnParam::Missing { placeholder, .. } => {
                placeholder.ty.as_deref_mut().map(|t| t.mono_mut())
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncSig {
    pub path: Node<Path>,
    pub params: Vec<Node<FnParam>>,
    pub ty_params: Option<TypeParams>,
    pub ret_ty: Option<Parsed<Ty>>,
    pub ty: Option<TyScheme>,
    pub modifiers: Vec<Modifier>,
    pub qualifiers: Vec<Parsed<Ty>>,
    pub doc_comment: Option<String>,
    pub is_anon: bool,
    pub is_method: bool,
    pub has_body: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Func {
    pub sig: FuncSig,
    pub body: Option<Box<Node<Expr>>>,
}

impl Func {
    pub fn new(path: Node<Path>, params: Vec<Node<FnParam>>, body: Node<Expr>) -> Self {
        Self {
            sig: FuncSig {
                path,
                params,
                ty_params: None,
                ret_ty: None,
                ty: None,
                modifiers: vec![],
                qualifiers: vec![],
                doc_comment: None,
                is_method: false,
                is_anon: false,
                has_body: true,
                span: Span::new(),
            },
            body: Some(Box::new(body)),
        }
    }

    pub fn to_sig_status(&self) -> SignatureStatus {
        // Check if all parameters have type annotations
        let all_params_annotated = self.sig.params.iter().all(|p| p.value.ty().is_some());
        if !all_params_annotated {
            return SignatureStatus::Unannotated;
        }

        // All params are annotated, check return type
        if self.sig.ret_ty.is_some() {
            return SignatureStatus::FullyAnnotated;
        }

        // Check if body is an arrow expression (not a block)
        // Arrow body: fn foo(x: int) => x + 1  -> ReturnElided (annotated)
        // Block body: fn foo(x: int) { x + 1 } -> Unannotated (missing return type is an error)
        let body_is_block = self
            .body
            .as_ref()
            .map(|b| matches!(b.value, Expr::Block(_)))
            .unwrap_or(true); // No body = treat as block (unannotated)

        if body_is_block {
            // Block body without return type annotation is unannotated
            SignatureStatus::Unannotated
        } else {
            // Arrow body (=>) - return type inferred from expression
            SignatureStatus::ReturnElided
        }
    }
}

impl std::fmt::Display for FuncSig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ty_params = if let Some(ref ty_params) = self.ty_params {
            ty_params.to_string()
        } else {
            String::new()
        };
        let ret_ty = self
            .ret_ty
            .as_ref()
            .map_or_else(|| "".to_string(), |t| format!(" -> {}", t));
        write!(
            f,
            "{}{}({}){}",
            self.path.name().unwrap_or_else(|| "__anon__".to_string()),
            ty_params,
            self.params
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            ret_ty,
        )
    }
}

impl std::fmt::Display for Func {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let body = self.body.as_ref();
        write!(
            f,
            "(fn {}{}{})",
            self.sig,
            if body
                .map(|body| { !matches!(body.value, Expr::Block(_)) })
                .unwrap_or_default()
            {
                " => "
            } else {
                "\n"
            },
            body.map_or_else(|| str!(""), |b| b.to_string()),
        )
    }
}

impl FuncSig {
    pub fn resolve_signature(
        &mut self,
        scopes: &Vec<Scope>,
        ncx: &NameContext,
    ) -> Result<(), RayError> {
        log::debug!("[resolve_signature] {}", self);

        // first, resolve all FQNs in the signature: type params, params, return type, qualifiers
        if let Some(ty_params) = self.ty_params.as_mut() {
            for ty_param in ty_params.tys.iter_mut() {
                ty_param.resolve_fqns(scopes, ncx);
            }
        }

        for param in self.params.iter_mut() {
            if let Some(ty) = param.ty_mut() {
                ty.resolve_fqns(scopes, ncx);
            }
        }

        if let Some(ret_ty) = self.ret_ty.as_mut() {
            ret_ty.resolve_fqns(scopes, ncx);
        }

        for qual in self.qualifiers.iter_mut() {
            qual.resolve_fqns(scopes, ncx);
        }
        Ok(())
    }

    /// Extract a type scheme from a function signature.
    ///
    /// Builds a `TyScheme` from the signature's type parameters, qualifiers,
    /// parameter types, and return type.
    pub fn extract_scheme(&self, subst: Option<&Subst>) -> TyScheme {
        // Extract type variables from type parameters
        let vars: Vec<TyVar> = self
            .ty_params
            .as_ref()
            .map(|tp| {
                tp.tys
                    .iter()
                    .filter_map(|parsed_ty| {
                        if let Ty::Var(v) = parsed_ty.value() {
                            Some(v.clone())
                        } else {
                            None
                        }
                    })
                    .collect()
            })
            .unwrap_or_default();

        // Extract parameter types
        let param_tys: Vec<Ty> = self
            .params
            .iter()
            .filter_map(|param| param.value.ty().cloned())
            .collect();

        // Extract return type, defaulting to unit/void
        let ret_ty = self
            .ret_ty
            .as_ref()
            .map(|parsed| parsed.deref().clone())
            .unwrap_or(Ty::unit());

        // Build the function type
        let func_ty = Ty::Func(param_tys, Box::new(ret_ty));

        // Extract qualifiers from the qualifiers into Predicates
        let mut qualifiers = vec![];
        if self.qualifiers.len() != 0 {
            for q in self.qualifiers.iter() {
                let (path, ty_args) = match q.value() {
                    Ty::Proj(name, args) => (name.clone(), args.clone()),
                    Ty::Const(name) => (name.clone(), vec![]),
                    _ => continue,
                };

                qualifiers.push(Predicate::class(path, ty_args));
            }
        }

        let mut scheme = TyScheme::new(vars, qualifiers, func_ty);
        if let Some(subst) = subst {
            scheme.apply_subst(subst);
        }
        scheme
    }

    pub fn fresh_scheme(
        &mut self,
        fn_scope: &Path,
        filepath: &FilePath,
        tcx: &mut TyCtx,
        srcmap: &SourceMap,
    ) -> Result<(), RayError> {
        // then create a "fresh" scheme, replacing each schema variable with a meta variable
        let ty = self.to_scheme(fn_scope, filepath, tcx, srcmap)?;
        if let Some(ty_params) = &mut self.ty_params {
            for ty_param in ty_params.tys.iter_mut() {
                let ty = ty_param.deref_mut();
                tcx.map_vars(ty);
            }
        }

        self.ty = Some(ty);
        Ok(())
    }

    pub fn to_scheme(
        &self,
        _fn_scope: &Path,
        _filepath: &FilePath,
        _fn_tcx: &mut TyCtx,
        _srcmap: &SourceMap,
    ) -> Result<TyScheme, RayError> {
        unreachable!("legacy code should not be called")
        // let mut param_tys = vec![];

        // for param in self.params.iter() {
        //     if let Some(ty) = param.ty() {
        //         log::debug!(
        //             "[FuncSig::to_scheme] resolving FQNs for func param: {:?}",
        //             param
        //         );
        //         let mut ty = ty.clone();
        //         fn_tcx.map_vars(&mut ty);
        //         param_tys.push(ty);
        //     } else {
        //         return Err(RayError {
        //             msg: format!("parameter `{}` must have a type annotation", param),
        //             src: vec![Source {
        //                 span: Some(srcmap.span_of(&param)),
        //                 filepath: filepath.clone(),
        //                 ..Default::default()
        //             }],
        //             kind: RayErrorKind::Type,
        //             context: Some("function signature type inference".to_string()),
        //         });
        //     }
        // }

        // let mut ret_ty = self.ret_ty.as_deref().cloned().unwrap_or_else(|| {
        //     if self.has_body {
        //         Ty::ret_placeholder(fn_scope)
        //     } else {
        //         Ty::unit()
        //     }
        // });
        // fn_tcx.map_vars(&mut ret_ty);

        // let ty = Ty::Func(param_tys, Box::new(ret_ty));

        // let mut preds = vec![];
        // if self.qualifiers.len() != 0 {
        //     for q in self.qualifiers.iter() {
        //         let ty_span = *q.span().unwrap();
        //         let mut q = q.clone_value();
        //         fn_tcx.map_vars(&mut q);

        //         let (fqn, ty_args) = match q {
        //             Ty::Proj(name, args) => (name, args),
        //             Ty::Const(name) => (name, vec![]),
        //             _ => {
        //                 return Err(RayError {
        //                     msg: str!("qualifier must be a trait type"),
        //                     src: vec![Source {
        //                         span: Some(ty_span),
        //                         filepath: filepath.clone(),
        //                         ..Default::default()
        //                     }],
        //                     kind: RayErrorKind::Type,
        //                     context: Some("function signature type inference".to_string()),
        //                 });
        //             }
        //         };

        //         log::debug!("converting from ast type: {}", fqn);
        //         if fn_tcx.get_trait_ty(&fqn).is_none() {
        //             return Err(RayError {
        //                 msg: format!("trait `{}` is not defined", fqn),
        //                 src: vec![Source {
        //                     span: Some(ty_span),
        //                     filepath: filepath.clone(),
        //                     ..Default::default()
        //                 }],
        //                 kind: RayErrorKind::Type,
        //                 context: Some("function signature type inference".to_string()),
        //             });
        //         }

        //         preds.push(Predicate::class(
        //             fqn.without_type_args().to_string(),
        //             ty_args,
        //         ));
        //     }
        // }

        // let vars = if let Some(ty_params) = &self.ty_params {
        //     let mut vars = vec![];
        //     for ty_param in ty_params.tys.iter() {
        //         let mut ty = ty_param.deref().clone();
        //         fn_tcx.map_vars(&mut ty);
        //         if let Ty::Var(v) = ty {
        //             vars.push(v);
        //         }
        //     }

        //     vars
        // } else {
        //     let mut vars = ty
        //         .free_vars()
        //         .into_iter()
        //         .chain(
        //             preds
        //                 .iter()
        //                 .flat_map(|q| {
        //                     let Predicate::Class(pred) = q else {
        //                         return None;
        //                     };

        //                     Some(&pred.args)
        //                 })
        //                 .flatten()
        //                 .flat_map(|ty| {
        //                     let Ty::Var(v) = ty else { return None };
        //                     Some(v)
        //                 }),
        //         )
        //         .filter(|tv| !tv.is_ret_placeholder())
        //         .cloned()
        //         .collect::<Vec<_>>();
        //     vars.sort();
        //     vars.dedup();
        //     vars
        // };

        // let scheme = if vars.len() != 0 || preds.len() != 0 {
        //     TyScheme::new(vars, preds, ty)
        // } else {
        //     TyScheme::from_mono(ty)
        // };

        // log::debug!("ty = {}", scheme);
        // Ok(scheme)
    }
}

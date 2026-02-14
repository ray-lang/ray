use std::collections::HashSet;
use std::ops::Deref as _;

use ray_shared::{
    def::SignatureStatus,
    pathlib::Path,
    span::{Span, parsed::Parsed},
    ty::{Ty, TyVar},
};
use ray_typing::{
    constraints::Predicate,
    types::{Subst, Substitutable, TyScheme},
};

use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Missing, Modifier, Name, Node, TypeParams};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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

    pub fn to_sig_status(&self, has_implicit_self: bool) -> SignatureStatus {
        let has_block_body = self
            .body
            .as_ref()
            .map(|b| matches!(b.value, Expr::Block(_)))
            .unwrap_or(true); // No body = treat as block
        self.sig.to_sig_status(has_implicit_self, has_block_body)
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
    /// Compute the signature status for this function signature.
    ///
    /// `has_implicit_self` — bare `self` is implicitly typed (e.g. in impl/trait methods).
    /// `has_block_body` — whether the body is a block (`{ ... }`) vs an arrow (`=> ...`).
    ///   Used to distinguish `ImplicitUnit` from `ReturnElided` when return type is missing.
    pub fn to_sig_status(&self, has_implicit_self: bool, has_block_body: bool) -> SignatureStatus {
        let all_params_annotated = self
            .params
            .iter()
            .all(|p| p.value.ty().is_some() || (has_implicit_self && p.value.name().is_self()));
        if !all_params_annotated {
            return SignatureStatus::Unannotated;
        }

        if self.ret_ty.is_some() {
            return SignatureStatus::FullyAnnotated;
        }

        if has_block_body {
            SignatureStatus::ImplicitUnit
        } else {
            SignatureStatus::ReturnElided
        }
    }

    /// Collect all type variables from this signature: explicit (from `ty_params`)
    /// and implicit (discovered from param types, return type, and qualifiers).
    ///
    /// Returns unique type vars in discovery order (explicit first, then implicit).
    pub fn all_type_vars(&self) -> Vec<TyVar> {
        let mut seen = HashSet::new();
        let mut out = Vec::new();

        // 1. Explicit type params first
        if let Some(tp) = &self.ty_params {
            for parsed_ty in &tp.tys {
                if let Ty::Var(tv) = parsed_ty.value() {
                    if let Some(name) = tv.path().name() {
                        if seen.insert(name) {
                            out.push(tv.clone());
                        }
                    }
                }
            }
        }

        // Collect user type vars from a Ty using existing free_vars()
        let mut collect = |ty: &Ty| {
            for tv in ty.free_vars() {
                if tv.is_user_var() {
                    if let Some(name) = tv.path().name() {
                        if seen.insert(name) {
                            out.push(tv.clone());
                        }
                    }
                }
            }
        };

        // 2. From param types
        for param in &self.params {
            if let Some(ty) = param.value.ty() {
                collect(ty);
            }
        }

        // 3. From return type
        if let Some(ret) = &self.ret_ty {
            collect(ret.value());
        }

        // 4. From qualifiers
        for qual in &self.qualifiers {
            collect(qual.value());
        }

        out
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
}

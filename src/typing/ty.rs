use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
    ops::{BitOr, Deref, DerefMut},
    str::FromStr,
};

use serde::{Deserialize, Serialize};
use top::{directives::TypeClassDirective, Predicate, Predicates, Subst, Substitutable};

use crate::{
    ast::{self, FuncSig, Path, TraitDirective},
    convert::ToSet,
    errors::{RayError, RayErrorKind},
    lir::Size,
    pathlib::FilePath,
    span::{Source, SourceMap},
    utils::{join, replace, DrainInPlace},
};

use super::{
    context::TyCtx,
    info::TypeSystemInfo,
    traits::QualifyTypes,
    // predicate::TyPredicate,
    // state::TyVarFactory,
    // subst::{ApplySubst, Subst},
    // traits::{
    //     CollectTyVars, Generalize, HasFreeVars, HoistTypes, Instantiate, Polymorphize, Skolemize,
    // },
    TypeError,
};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TyScheme(top::SchemePredicates<Ty, TyVar>);

impl Deref for TyScheme {
    type Target = top::SchemePredicates<Ty, TyVar>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for TyScheme {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Display for TyScheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Into<SigmaTy> for TyScheme {
    fn into(self) -> SigmaTy {
        SigmaTy::scheme(self)
    }
}

impl Default for TyScheme {
    fn default() -> Self {
        Self::from_mono(Ty::unit())
    }
}

impl QualifyTypes for TyScheme {
    fn qualify_tys(&mut self, preds: &Vec<Predicate<Ty, TyVar>>) {
        let freevars = self.free_vars();
        let preds = preds
            .iter()
            .filter(|pred| pred.free_vars().iter().any(|var| freevars.contains(var)))
            .cloned()
            .collect::<Vec<_>>();
        self.ty.qualifiers_mut().extend(preds);
        self.ty.qualifiers_mut().sort();
        self.ty.qualifiers_mut().dedup();
    }
}

impl TyScheme {
    pub fn new(vars: Vec<TyVar>, preds: Predicates<Ty, TyVar>, ty: Ty) -> Self {
        Self(top::SchemePredicates::new(
            vars,
            top::Qualification::new(preds, ty),
        ))
    }

    pub fn scheme(scheme: top::SchemePredicates<Ty, TyVar>) -> Self {
        Self(scheme)
    }

    #[inline(always)]
    pub fn from_var(var: TyVar) -> Self {
        Self::from_mono(Ty::Var(var))
    }

    #[inline(always)]
    pub fn from_mono(ty: Ty) -> Self {
        Self(top::SchemePredicates::mono(
            top::Qualification::unqualified(ty),
        ))
    }

    pub fn from_sig(
        sig: &FuncSig,
        fn_scope: &Path,
        filepath: &FilePath,
        fn_tcx: &mut TyCtx,
        srcmap: &SourceMap,
    ) -> Result<Self, RayError> {
        let mut param_tys = vec![];

        for param in sig.params.iter() {
            if let Some(ty) = param.ty() {
                let mut ty = ty.clone();
                ty.resolve_fqns(&fn_scope, fn_tcx);
                ty.map_vars(fn_tcx);
                param_tys.push(ty);
            } else {
                return Err(RayError {
                    msg: format!("parameter `{}` must have a type annotation", param),
                    src: vec![Source {
                        span: Some(srcmap.span_of(&param)),
                        filepath: filepath.clone(),
                        ..Default::default()
                    }],
                    kind: RayErrorKind::Type,
                });
            }
        }

        let mut ret_ty = sig.ret_ty.as_deref().cloned().unwrap_or_else(|| {
            if sig.has_body {
                Ty::ret_placeholder(fn_scope)
            } else {
                Ty::unit()
            }
        });
        ret_ty.resolve_fqns(&fn_scope, fn_tcx);
        ret_ty.map_vars(fn_tcx);

        let ty = Ty::Func(param_tys, Box::new(ret_ty));

        let vars = if let Some(ty_params) = &sig.ty_params {
            let mut vars = vec![];
            for ty_param in ty_params.tys.iter() {
                let mut ty = ty_param.deref().clone();
                ty.map_vars(fn_tcx);
                if let Ty::Var(v) = ty {
                    vars.push(v.clone());
                }
            }

            vars
        } else {
            let mut vars = ty
                .free_vars()
                .into_iter()
                .filter(|tv| !tv.is_ret_placeholder())
                .cloned()
                .collect::<Vec<_>>();
            vars.sort();
            vars.dedup();
            vars
        };

        let scheme = if sig.qualifiers.len() != 0 {
            let mut preds = Predicates::new();
            for q in sig.qualifiers.iter() {
                let ty_span = *q.span().unwrap();
                let mut q = q.clone_value();
                q.resolve_fqns(fn_scope, fn_tcx);
                q.map_vars(fn_tcx);

                let (s, v) = match q {
                    Ty::Projection(s, v) => (s.name(), v),
                    Ty::Const(name) => (name, vec![]),
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

                let mut ty_arg = v[0].clone();
                ty_arg.map_vars(fn_tcx);
                let fqn = Path::from(s.as_str());
                log::debug!("converting from ast type: {}", fqn);
                if fn_tcx.get_trait_ty(&fqn).is_none() {
                    return Err(RayError {
                        msg: format!("trait `{}` is not defined", fqn),
                        src: vec![Source {
                            span: Some(ty_span),
                            filepath: filepath.clone(),
                            ..Default::default()
                        }],
                        kind: RayErrorKind::Type,
                    });
                }

                preds.push(Predicate::class(fqn.to_string(), ty_arg));
            }
            Self::new(vars, preds, ty)
        } else if vars.len() != 0 {
            Self::new(vars, Predicates::new(), ty)
        } else {
            Self::from_mono(ty)
        };

        log::debug!("ty = {}", scheme);
        Ok(scheme)
    }

    pub fn mono(&self) -> &Ty {
        &self.ty.ty
    }

    pub fn mono_mut(&mut self) -> &mut Ty {
        &mut self.ty.ty
    }

    pub fn into_mono(self) -> Ty {
        // NOTE: should this actual fail if not actually a monotype?
        self.0.ty.ty
    }

    pub fn has_quantifiers(&self) -> bool {
        !self.vars.is_empty()
    }

    #[inline(always)]
    pub fn has_freevars(&self) -> bool {
        !self.free_vars().is_empty()
    }

    #[inline(always)]
    pub fn is_polymorphic(&self) -> bool {
        self.has_quantifiers() || self.has_freevars()
    }

    pub fn quantifiers(&self) -> &Vec<TyVar> {
        &self.vars
    }

    pub fn qualifiers(&self) -> &Predicates<Ty, TyVar> {
        &self.ty.qualifiers
    }

    pub fn is_unit(&self) -> bool {
        self.ty.ty.is_unit()
    }

    pub fn take(self) -> top::SchemePredicates<Ty, TyVar> {
        self.0
    }

    pub fn try_borrow_fn(&self) -> Option<(&Vec<TyVar>, &Predicates<Ty, TyVar>, &Vec<Ty>, &Ty)> {
        if let Ty::Func(params, ret) = &self.ty.ty {
            Some((&self.vars, &self.ty.qualifiers, params, ret))
        } else {
            None
        }
    }

    pub fn resolve_fqns(&mut self, scope: &ast::Path, tcx: &mut TyCtx) {
        self.unquantified_mut().ty_mut().resolve_fqns(scope, tcx)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SigmaTy(top::SigmaPredicates<Ty, TyVar>);

impl Deref for SigmaTy {
    type Target = top::SigmaPredicates<Ty, TyVar>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for SigmaTy {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Display for SigmaTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.deref() {
            top::SigmaPredicates::Var(v) => write!(f, "{}", v),
            top::SigmaPredicates::Scheme(s) => {
                write!(f, "{}", s)
            }
        }
    }
}

impl SigmaTy {
    pub fn var(var: TyVar) -> Self {
        SigmaTy(top::SigmaPredicates::Var(var))
    }

    pub fn scheme(scheme: TyScheme) -> Self {
        SigmaTy(top::SigmaPredicates::Scheme(scheme.take()))
    }

    pub fn mono(ty: Ty) -> Self {
        SigmaTy(top::SigmaPredicates::mono(ty))
    }

    #[inline(always)]
    pub fn is_polymorphic(&self) -> bool {
        self.has_quantifiers()
    }

    pub fn get_mono(&self) -> Option<&Ty> {
        match &self.0 {
            top::SigmaPredicates::Scheme(sch)
                if sch.vars.is_empty() && sch.ty.qualifiers.is_empty() =>
            {
                Some(&sch.ty.ty)
            }
            _ => None,
        }
    }

    pub fn into_mono(self) -> Option<Ty> {
        match self.0 {
            top::SigmaPredicates::Scheme(sch)
                if sch.vars.is_empty() && sch.ty.qualifiers.is_empty() =>
            {
                Some(sch.ty.ty)
            }
            _ => None,
        }
    }

    pub fn get_mono_mut(&mut self) -> Option<&mut Ty> {
        match &mut self.0 {
            top::SigmaPredicates::Scheme(sch)
                if sch.vars.is_empty() && sch.ty.qualifiers.is_empty() =>
            {
                Some(&mut sch.ty.ty)
            }
            _ => None,
        }
    }

    pub fn get_scheme(&self) -> Option<&top::SchemePredicates<Ty, TyVar>> {
        match &self.0 {
            top::SigmaPredicates::Scheme(sch) => Some(sch),
            _ => None,
        }
    }

    pub fn get_scheme_mut(&mut self) -> Option<&mut top::SchemePredicates<Ty, TyVar>> {
        match &mut self.0 {
            top::SigmaPredicates::Scheme(sch) => Some(sch),
            _ => None,
        }
    }

    pub fn has_quantifiers(&self) -> bool {
        match &self.0 {
            top::SigmaPredicates::Scheme(sch) => !sch.vars.is_empty(),
            _ => false,
        }
    }

    pub fn quantifiers(&self) -> Option<&Vec<TyVar>> {
        match &self.0 {
            top::Sigma::Scheme(sch) => Some(sch.quantifiers()),
            _ => None,
        }
    }

    pub fn take(self) -> top::SigmaPredicates<Ty, TyVar> {
        self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct TyVar(pub Path);

impl<P> From<P> for TyVar
where
    P: Into<Path>,
{
    fn from(p: P) -> Self {
        TyVar(p.into())
    }
}

impl std::fmt::Display for TyVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
        // if f.alternate() {
        //     write!(f, "{}", self.0)
        // } else {
        //     if let Some(name) = self.0.name() {
        //         write!(f, "{}", name)
        //     } else {
        //         write!(f, "")
        //     }
        // }
    }
}

// impl ApplySubst for TyVar {
//     fn apply_subst(self, subst: &Subst) -> TyVar {
//         subst.get_var(self)
//     }
// }

// impl Polymorphize for TyVar {
//     fn polymorphize(self, tf: &mut TyVarFactory, subst: &mut HashMap<Ty, TyVar>) -> Self {
//         if let Some(tv) = subst.get(&Ty::Var(self.clone())) {
//             tv.clone()
//         } else {
//             let path = self.path().parent();
//             let tv = tf.with_scope(&path);
//             subst.insert(Ty::Var(self), tv.clone());
//             tv
//         }
//     }
// }

impl FromStr for TyVar {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(TyVar::new(Path::from(s)))
    }
}

impl top::TyVar for TyVar {
    fn from_u32(u: u32) -> Self {
        TyVar::new(Path::from(format!("?t{}", u)))
    }

    fn get_u32(&self) -> Option<u32> {
        self.path()
            .name()?
            .chars()
            .filter(|c| c.is_ascii_digit())
            .collect::<String>()
            .parse::<u32>()
            .ok()
    }
}

impl Default for TyVar {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl TyVar {
    pub fn new<P: Into<Path>>(p: P) -> TyVar {
        TyVar(p.into())
    }

    #[inline(always)]
    pub fn path(&self) -> &Path {
        &self.0
    }

    #[inline(always)]
    pub fn path_mut(&mut self) -> &mut Path {
        &mut self.0
    }

    #[inline(always)]
    pub fn is_ret_placeholder(&self) -> bool {
        matches!(self.path().name().as_deref(), Some(n) if n.starts_with("%r"))
    }

    #[inline(always)]
    pub fn is_unknown(&self) -> bool {
        matches!(self.path().name().as_deref(), Some(n) if n.starts_with("?"))
    }

    // pub fn to_u32(&self) -> u32 {
    //     let mut hasher = DefaultHasher::new();
    //     self.hash(&mut hasher);
    //     (hasher.finish() % (u32::MAX as u64)) as u32
    // }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StructTy {
    pub path: ast::Path,
    pub ty: TyScheme,
    pub fields: Vec<(String, TyScheme)>,
}

impl Hash for StructTy {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.path.hash(state);
    }
}

impl StructTy {
    pub fn get_field(&self, f: &String) -> Option<(usize, &TyScheme)> {
        self.fields
            .iter()
            .enumerate()
            .find_map(|(idx, (g, t))| if f == g { Some((idx, t)) } else { None })
    }

    pub fn field_tys(&self) -> Vec<TyScheme> {
        self.fields.iter().map(|(_, t)| t.clone()).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraitTy {
    pub path: ast::Path,
    pub ty: Ty,
    pub super_traits: Vec<Ty>,
    pub fields: Vec<(String, TyScheme)>,
    pub directives: Vec<TypeClassDirective<TypeSystemInfo, Ty, TyVar>>,
}

impl TraitTy {
    pub fn field_tys(&self) -> Vec<TyScheme> {
        self.fields.iter().map(|(_, t)| t.clone()).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ImplTy {
    pub base_ty: Ty,
    pub trait_ty: Ty,
    pub predicates: Vec<Predicate<Ty, TyVar>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum LiteralKind {
    Int,
    Float,
}

impl std::fmt::Display for LiteralKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LiteralKind::Int => write!(f, "int literal"),
            LiteralKind::Float => write!(f, "float literal"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Ty {
    Never,
    Any,
    Var(TyVar),
    Tuple(Vec<Ty>),
    Ptr(Box<Ty>),
    Union(Vec<Ty>),
    Array(Box<Ty>, usize),
    Func(Vec<Ty>, Box<Ty>),
    Const(String),
    Projection(Box<Ty>, Vec<Ty>),
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Never => write!(f, "never"),
            Ty::Any => write!(f, "any"),
            Ty::Var(v) => {
                if f.alternate() {
                    write!(f, "{:#}", v)
                } else {
                    write!(f, "{}", v)
                }
            }
            Ty::Tuple(tys) => {
                write!(f, "({})", join(tys, ", "))
            }
            Ty::Ptr(ty) => {
                write!(f, "*{}", ty)
            }
            Ty::Union(tys) => {
                write!(f, "{}", join(tys, " | "))
            }
            Ty::Array(ty, size) => {
                write!(f, "[{}; {}]", ty, size)
            }
            Ty::Func(a, r) => write!(f, "({}) -> {}", join(a, ", "), r),
            Ty::Const(s) => write!(f, "{}", s),
            Ty::Projection(n, t) => {
                if t.len() != 0 {
                    write!(f, "{}[{}]", n, join(t, ", "))
                } else {
                    write!(f, "{}", n)
                }
            }
        }
    }
}

impl Default for Ty {
    fn default() -> Ty {
        Ty::unit()
    }
}

impl Into<TyScheme> for Ty {
    fn into(self) -> TyScheme {
        TyScheme::from_mono(self)
    }
}

impl BitOr for Ty {
    type Output = Ty;

    fn bitor(self, rhs: Ty) -> Ty {
        match (self, rhs) {
            (Ty::Union(lhs_tys), Ty::Union(rhs_tys)) => {
                let mut set = lhs_tys
                    .into_iter()
                    .chain(rhs_tys.into_iter())
                    .collect::<Vec<_>>();
                set.dedup();
                Ty::Union(set)
            }
            (Ty::Union(mut tys), t) => {
                tys.push(t);
                Ty::Union(tys)
            }
            (t, Ty::Union(mut tys)) => {
                tys.push(t);
                Ty::Union(tys)
            }
            (s, t) => Ty::Union(vec![s, t]),
        }
    }
}

impl Substitutable<TyVar, Ty> for Ty {
    fn apply_subst(&mut self, subst: &Subst<TyVar, Ty>) {
        match self {
            Ty::Any | Ty::Never | Ty::Const(_) => {}
            Ty::Var(var) => {
                *self = subst.lookup_var(var);
            }
            Ty::Projection(ty, tys) => {
                ty.apply_subst(subst);
                tys.apply_subst(subst);
            }
            Ty::Tuple(tys) | Ty::Union(tys) => tys.apply_subst(subst),
            Ty::Ptr(ty) | Ty::Array(ty, _) => {
                ty.apply_subst(subst);
            }
            Ty::Func(param_tys, ret_ty) => {
                param_tys.apply_subst(subst);
                ret_ty.apply_subst(subst);
            }
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<TyVar, Ty>) {
        match self {
            Ty::Any | Ty::Never | Ty::Const(_) => {}
            Ty::Var(var) => {
                *self = subst.lookup_var(var);
            }
            Ty::Projection(ty, tys) => {
                ty.apply_subst_all(subst);
                tys.apply_subst_all(subst);
            }
            Ty::Tuple(tys) | Ty::Union(tys) => tys.apply_subst_all(subst),
            Ty::Ptr(ty) | Ty::Array(ty, _) => {
                ty.apply_subst_all(subst);
            }
            Ty::Func(param_tys, ret_ty) => {
                param_tys.apply_subst_all(subst);
                ret_ty.apply_subst_all(subst);
            }
        }
    }

    fn free_vars(&self) -> Vec<&TyVar> {
        match self {
            Ty::Never | Ty::Any | Ty::Const(_) => vec![],
            Ty::Var(v) => vec![v],
            Ty::Projection(ty, tys) => {
                let mut vars = ty.free_vars();
                vars.extend(tys.free_vars());
                vars
            }
            Ty::Tuple(tys) | Ty::Union(tys) => tys.free_vars(),
            Ty::Ptr(ty) | Ty::Array(ty, _) => ty.free_vars(),
            Ty::Func(param_tys, ret_ty) => {
                let mut vars = param_tys.free_vars();
                vars.extend(ret_ty.free_vars());
                vars
            }
        }
    }
}

impl top::Ty<TyVar> for Ty {
    fn new(name: &str) -> Self {
        Self::Const(name.to_string())
    }

    fn var(v: TyVar) -> Self {
        Self::Var(v)
    }

    fn app(lhs: Self, rhs: Self) -> Self {
        Ty::Projection(Box::new(lhs), vec![rhs])
    }

    fn tuple(tys: Vec<Self>) -> Self {
        Ty::Tuple(tys)
    }

    fn maybe_var(&self) -> Option<&TyVar> {
        match self {
            Ty::Var(v) => Some(v),
            _ => None,
        }
    }

    fn maybe_const(&self) -> Option<&str> {
        match self {
            Ty::Const(n) => Some(n),
            _ => None,
        }
    }

    fn maybe_app(&self) -> Option<(Self, Vec<Self>)> {
        match self {
            Ty::Any => Some((Ty::Const(str!("any")), vec![])),
            Ty::Never => Some((Ty::Const(str!("never")), vec![])),
            Ty::Array(ty, size) => {
                Some((Ty::Const(format!("[{}]", size)), vec![ty.as_ref().clone()]))
            }
            Ty::Projection(n, tys) => Some((n.as_ref().clone(), tys.clone())),
            Ty::Ptr(ty) => Some((Ty::Const(str!("*")), vec![ty.as_ref().clone()])),
            _ => None,
        }
    }

    fn maybe_func(&self) -> Option<(&Vec<Self>, &Self)> {
        match self {
            Ty::Func(param_tys, ret_ty) => Some((param_tys, ret_ty)),
            _ => None,
        }
    }

    fn maybe_tuple(&self) -> Option<&Vec<Self>> {
        match self {
            Ty::Tuple(tys) => Some(tys),
            _ => None,
        }
    }

    fn is_tyvar(&self) -> bool {
        matches!(self, Ty::Var(_))
    }

    fn in_head_normal_form(&self) -> bool {
        match self {
            Ty::Var(_) => true,
            Ty::Any | Ty::Never | Ty::Const(_) | Ty::Func(_, _) => false,
            Ty::Tuple(tys) | Ty::Union(tys) => tys.iter().all(|ty| ty.in_head_normal_form()),
            Ty::Array(ty, _) | Ty::Ptr(ty) | Ty::Projection(ty, _) => ty.in_head_normal_form(),
        }
    }

    fn name(&self) -> &str {
        match self {
            Ty::Never => "never",
            Ty::Any => "any",
            Ty::Var(_) => todo!(),
            Ty::Tuple(_) => todo!(),
            Ty::Ptr(_) => todo!(),
            Ty::Union(_) => todo!(),
            Ty::Array(_, _) => todo!(),
            Ty::Func(_, _) => todo!(),
            Ty::Const(n) => n,
            Ty::Projection(ty, _) => top::Ty::name(ty.as_ref()),
        }
    }

    fn variables(&self) -> Vec<&TyVar>
    where
        TyVar: Ord,
    {
        match self {
            Ty::Var(v) => vec![v],
            Ty::Tuple(tys) | Ty::Union(tys) => tys.iter().flat_map(|ty| ty.variables()).collect(),
            Ty::Projection(ty, tys) => {
                let mut vars = ty.variables();
                vars.extend(tys.iter().flat_map(|ty| ty.variables()));
                vars
            }
            Ty::Ptr(ty) | Ty::Array(ty, _) => ty.variables(),
            Ty::Func(param_tys, ret_ty) => {
                let mut vars = param_tys
                    .iter()
                    .flat_map(|ty| ty.variables())
                    .collect::<Vec<_>>();
                vars.extend(ret_ty.variables());
                vars
            }
            Ty::Const(_) => vec![],
            Ty::Any | Ty::Never => vec![],
        }
    }

    fn constants(&self) -> Vec<String> {
        match self {
            Ty::Any => vec![str!("any")],
            Ty::Never => vec![str!("never")],
            Ty::Var(_) => vec![],
            Ty::Const(n) => vec![n.clone()],
            Ty::Tuple(tys) | Ty::Union(tys) => tys.iter().flat_map(|ty| ty.constants()).collect(),
            Ty::Projection(ty, tys) => {
                let mut vars = ty.constants();
                vars.extend(tys.iter().flat_map(|ty| ty.constants()));
                vars
            }
            Ty::Ptr(ty) | Ty::Array(ty, _) => ty.constants(),
            Ty::Func(param_tys, ret_ty) => {
                let mut vars = param_tys
                    .iter()
                    .flat_map(|ty| ty.constants())
                    .collect::<Vec<_>>();
                vars.extend(ret_ty.constants());
                vars
            }
        }
    }

    fn eq_with_synonyms(
        &self,
        other: &Self,
        synonyms: &top::OrderedTypeSynonyms<Self, TyVar>,
    ) -> Option<Self> {
        todo!()
    }

    fn freeze_vars(&self) -> Self
    where
        TyVar: std::fmt::Display,
    {
        match self {
            Ty::Any | Ty::Never | Ty::Const(_) => self.clone(),
            Ty::Var(v) => Ty::Const(format!("//{}", v)),
            Ty::Tuple(tys) => Ty::Tuple(tys.iter().map(|ty| ty.freeze_vars()).collect()),
            Ty::Ptr(ty) => Ty::Ptr(Box::new(ty.freeze_vars())),
            Ty::Union(tys) => Ty::Union(tys.iter().map(|ty| ty.freeze_vars()).collect()),
            Ty::Array(ty, n) => Ty::Array(Box::new(ty.freeze_vars()), *n),
            Ty::Func(param_tys, ret_ty) => Ty::Func(
                param_tys.iter().map(|ty| ty.freeze_vars()).collect(),
                Box::new(ret_ty.freeze_vars()),
            ),
            Ty::Projection(ty, tys) => Ty::Projection(
                Box::new(ty.freeze_vars()),
                tys.iter().map(|ty| ty.freeze_vars()).collect(),
            ),
        }
    }

    fn unfreeze_vars(&self) -> Self
    where
        TyVar: FromStr,
        <TyVar as FromStr>::Err: std::fmt::Debug,
    {
        match self {
            Ty::Any | Ty::Never | Ty::Var(_) => self.clone(),
            Ty::Const(n) => {
                if n.starts_with("//") {
                    let chars = n.chars().skip(1).collect::<Vec<_>>();
                    if chars.len() != 0 && chars.iter().all(|c| c.is_ascii_digit()) {
                        let s = chars.iter().collect::<String>();
                        return Ty::Var(s.parse().unwrap());
                    }
                }

                Ty::Const(n.clone())
            }
            Ty::Tuple(tys) => Ty::Tuple(tys.iter().map(|ty| ty.unfreeze_vars()).collect()),
            Ty::Ptr(ty) => Ty::Ptr(Box::new(ty.unfreeze_vars())),
            Ty::Union(tys) => Ty::Union(tys.iter().map(|ty| ty.unfreeze_vars()).collect()),
            Ty::Array(ty, n) => Ty::Array(Box::new(ty.unfreeze_vars()), *n),
            Ty::Func(param_tys, ret_ty) => Ty::Func(
                param_tys.iter().map(|ty| ty.unfreeze_vars()).collect(),
                Box::new(ret_ty.unfreeze_vars()),
            ),
            Ty::Projection(ty, tys) => Ty::Projection(
                Box::new(ty.unfreeze_vars()),
                tys.iter().map(|ty| ty.unfreeze_vars()).collect(),
            ),
        }
    }
}

impl Ty {
    #[inline(always)]
    pub fn with_vars<T: ToString>(name: &T, vars: &[TyVar]) -> Self {
        Ty::with_tys(name, vars.iter().map(|t| Ty::Var(t.clone())).collect())
    }

    pub fn with_tys<T: ToString>(name: &T, tys: Vec<Ty>) -> Self {
        if tys.is_empty() {
            Ty::Const(name.to_string())
        } else {
            Ty::Projection(Box::new(Ty::Const(name.to_string())), tys)
        }
    }

    pub fn from_str(s: &str) -> Option<Ty> {
        Some(match s {
            "int" => Ty::int(),
            "i8" => Ty::i8(),
            "i16" => Ty::i16(),
            "i32" => Ty::i32(),
            "i64" => Ty::i64(),
            "i128" => Ty::i128(),
            "uint" => Ty::uint(),
            "u8" => Ty::u8(),
            "u16" => Ty::u16(),
            "u32" => Ty::u32(),
            "u64" => Ty::u64(),
            "u128" => Ty::u128(),
            "float" => Ty::float(),
            "f32" => Ty::f32(),
            "f64" => Ty::f64(),
            "f128" => Ty::f128(),
            "string" => Ty::string(),
            "char" => Ty::char(),
            "bool" => Ty::bool(),
            "list" => Ty::list(Ty::nil()),
            _ => return None,
        })
    }

    pub fn desc(&self) -> String {
        match self {
            Ty::Never => str!("never"),
            Ty::Any => str!("any"),
            Ty::Var(_) => str!("variable"),
            Ty::Tuple(_) => str!("tuple"),
            Ty::Ptr(ty) => format!("pointer of {}", ty.desc()),
            Ty::Union(_) => str!("union"),
            Ty::Array(ty, _) => format!("array of {}", ty.desc()),
            Ty::Func(_, _) => str!("function"),
            Ty::Const(name) => name.clone(),
            Ty::Projection(ty, _) => ty.desc(),
            // Ty::Qualified(_, ty) => ty.desc(),
            // Ty::All(_, ty) => ty.desc(),
        }
    }

    pub fn resolve_fqns(&mut self, scope: &ast::Path, tcx: &mut TyCtx) {
        match self {
            Ty::Const(name) => {
                if let Some(fqn) = tcx.lookup_fqn(name) {
                    *name = fqn.to_string();
                }
            }
            Ty::Projection(ty, tys) => {
                ty.resolve_fqns(scope, tcx);
                for ty in tys {
                    ty.resolve_fqns(scope, tcx);
                }
            }
            Ty::Tuple(tys) | Ty::Union(tys) => {
                tys.iter_mut().for_each(|t| t.resolve_fqns(scope, tcx));
            }
            Ty::Ptr(t) | Ty::Array(t, _) => t.resolve_fqns(scope, tcx),
            Ty::Func(params, ret) => {
                params.iter_mut().for_each(|t| t.resolve_fqns(scope, tcx));
                ret.resolve_fqns(scope, tcx);
            }
            Ty::Var(_) | Ty::Never | Ty::Any => {}
        }
    }

    pub fn map_vars(&mut self, tcx: &mut TyCtx) {
        match self {
            Ty::Never | Ty::Any | Ty::Const(_) => {}
            Ty::Var(tv) => {
                if tv.is_ret_placeholder() {
                    return;
                }

                *tv = if let Some(mapped_tv) = tcx.get_var_mapping(tv) {
                    log::debug!("found mapping: {} -> {}", tv, mapped_tv);
                    mapped_tv.clone()
                } else {
                    let mapped_tv = tcx.tf().next();
                    tcx.add_var_mapping(tv.clone(), mapped_tv.clone());
                    mapped_tv
                };
            }
            Ty::Tuple(tys) | Ty::Union(tys) => {
                tys.iter_mut().for_each(|t| t.map_vars(tcx));
            }
            Ty::Array(ty, _) | Ty::Projection(ty, _) | Ty::Ptr(ty) => ty.map_vars(tcx),
            Ty::Func(param_tys, ret_ty) => {
                param_tys.iter_mut().for_each(|t| t.map_vars(tcx));
                ret_ty.map_vars(tcx);
            }
        }
    }

    pub fn is_builtin(name: &str) -> bool {
        match name {
            "string" | "char" | "bool" | "int" | "uint" | "i8" | "i16" | "i32" | "i64" | "u8"
            | "u16" | "u32" | "u64" => true,
            _ => false,
        }
    }

    #[inline(always)]
    pub fn unit() -> Ty {
        Ty::Tuple(vec![])
    }

    #[inline(always)]
    pub fn var<P: Into<Path>>(s: P) -> Ty {
        Ty::Var(TyVar(s.into()))
    }

    #[inline(always)]
    pub fn ret_placeholder<P: Into<Path>>(p: P) -> Ty {
        Ty::Var(TyVar(p.into().append("%r")))
    }

    #[inline(always)]
    pub fn con<S: Into<String>>(s: S) -> Ty {
        Ty::Const(s.into())
    }

    #[inline(always)]
    pub fn ptr(ty: Ty) -> Ty {
        Ty::Ptr(Box::new(ty))
    }

    #[inline(always)]
    pub fn ty_type(ty: Ty) -> Ty {
        Ty::Projection(Box::new(Ty::Const(str!("type"))), vec![ty])
    }

    #[inline(always)]
    pub fn nil() -> Ty {
        Ty::con("nil")
    }

    #[inline(always)]
    pub fn bool() -> Ty {
        Ty::con("bool")
    }

    #[inline(always)]
    pub fn char() -> Ty {
        Ty::con("char")
    }

    #[inline(always)]
    pub fn string() -> Ty {
        Ty::Const(str!("string"))
    }

    #[inline(always)]
    pub fn bytes() -> Ty {
        Ty::con("bytes")
    }

    #[inline(always)]
    pub fn range(el: Ty) -> Ty {
        Ty::Projection(Box::new(Ty::Const(str!("range"))), vec![el.clone()])
    }

    #[inline(always)]
    pub fn list(el: Ty) -> Ty {
        Ty::Projection(Box::new(Ty::Const(str!("list"))), vec![el])
    }

    #[inline(always)]
    pub fn int() -> Ty {
        Ty::con("int")
    }

    #[inline(always)]
    pub fn i8() -> Ty {
        Ty::con("i8")
    }

    #[inline(always)]
    pub fn i16() -> Ty {
        Ty::con("i16")
    }

    #[inline(always)]
    pub fn i32() -> Ty {
        Ty::con("i32")
    }

    #[inline(always)]
    pub fn i64() -> Ty {
        Ty::con("i64")
    }

    #[inline(always)]
    pub fn i128() -> Ty {
        Ty::con("i128")
    }

    #[inline(always)]
    pub fn uint() -> Ty {
        Ty::con("uint")
    }

    #[inline(always)]
    pub fn u8() -> Ty {
        Ty::con("u8")
    }

    #[inline(always)]
    pub fn u16() -> Ty {
        Ty::con("u16")
    }

    #[inline(always)]
    pub fn u32() -> Ty {
        Ty::con("u32")
    }

    #[inline(always)]
    pub fn u64() -> Ty {
        Ty::con("u64")
    }

    #[inline(always)]
    pub fn u128() -> Ty {
        Ty::con("u128")
    }

    #[inline(always)]
    pub fn float() -> Ty {
        Ty::con("float")
    }

    #[inline(always)]
    pub fn f32() -> Ty {
        Ty::con("f32")
    }

    #[inline(always)]
    pub fn f64() -> Ty {
        Ty::con("f64")
    }

    #[inline(always)]
    pub fn f128() -> Ty {
        Ty::con("f128")
    }

    #[inline(always)]
    pub fn is_int_ty(&self) -> bool {
        match self {
            Ty::Const(a)
                if matches!(
                    a.as_str(),
                    "int"
                        | "i8"
                        | "i16"
                        | "i32"
                        | "i64"
                        | "i128"
                        | "uint"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "u128"
                ) =>
            {
                true
            }
            _ => false,
        }
    }

    #[inline(always)]
    pub fn is_float_ty(&self) -> bool {
        match self {
            Ty::Const(a) if matches!(a.as_str(), "float" | "f32" | "f64" | "f128") => true,
            _ => false,
        }
    }

    #[inline(always)]
    pub fn get_path(&self) -> Option<Path> {
        match self {
            Ty::Never => Some(Path::from("never")),
            Ty::Any => Some(Path::from("any")),
            Ty::Var(v) => Some(v.path().clone()),
            Ty::Const(s) => Some(Path::from(s.clone())),
            Ty::Projection(ty, _) => ty.get_path(),
            Ty::Array(..) | Ty::Ptr(_) | Ty::Tuple(_) | Ty::Union(_) | Ty::Func(_, _) => None,
        }
    }

    pub fn name(&self) -> String {
        match self {
            Ty::Never => str!("never"),
            Ty::Any => str!("any"),
            Ty::Tuple(_) => str!("tuple"),
            Ty::Var(v) => v.path().name().unwrap(),
            Ty::Const(s) => s.clone(),
            Ty::Projection(ty, _) => ty.name(),
            Ty::Array(..) | Ty::Ptr(_) | Ty::Union(_) | Ty::Func(_, _) => {
                str!("")
            }
        }
    }

    pub fn size_of(&self) -> Size {
        match self {
            Ty::Never | Ty::Any | Ty::Var(_) => Size::zero(),
            Ty::Array(t, size) => t.size_of() * *size,
            Ty::Tuple(t) => t.iter().map(Ty::size_of).sum(),
            Ty::Union(v) => {
                let tag_size = (v.len() + 7) / 8;
                let max_size = v.iter().map(Ty::size_of).max().unwrap_or_default();
                Size::bytes(tag_size) + max_size
            }
            Ty::Func(_, _) | Ty::Ptr(_) => Size::ptr(),
            Ty::Projection(ty, _) => ty.size_of(),
            Ty::Const(n) => match n.as_str() {
                "int" | "uint" => Size::ptr(),
                "i8" | "u8" | "bool" => Size::bytes(1),
                "i16" | "u16" => Size::bytes(2),
                "i32" | "u32" | "f32" => Size::bytes(4),
                "i64" | "u64" | "f64" => Size::bytes(8),
                "i128" | "u128" | "f128" => Size::bytes(16),
                _ => Size::ptr(),
            },
        }
    }

    // pub fn skolemize_freevars(self) -> Ty {
    //     match self {
    //         Ty::All(xs, t) => {
    //             let consts = xs
    //                 .iter()
    //                 .enumerate()
    //                 .map(|(i, _)| Ty::Var(TyVar::from(format!("${}", i))))
    //                 .collect::<Vec<_>>();
    //             let sub = Subst::from_types(xs.clone(), consts);
    //             Ty::All(xs, t).apply_subst(&sub)
    //         }
    //         t @ _ => t,
    //     }
    // }

    // pub fn quantify(self, tyvars: Vec<TyVar>) -> Ty {
    //     if tyvars.len() != 0 {
    //         let t = match self {
    //             Ty::All(_, t) => t,
    //             _ => Box::new(self),
    //         };
    //         Ty::All(tyvars, t)
    //     } else {
    //         self
    //     }
    // }

    // pub fn quantify_in_place(&mut self) {
    //     let freevars = HashSet::new();
    //     replace(self, |ty| ty.quantify_with_freevars(&freevars));
    // }

    // pub fn quantify_with_freevars(self, freevars: &HashSet<&TyVar>) -> Ty {
    //     let mut tyvars = self.collect_tyvars();
    //     let mut i = 0;
    //     while i < tyvars.len() {
    //         let t = &tyvars[i];
    //         if t.is_ret_placeholder() || freevars.contains(&t) {
    //             tyvars.remove(i);
    //         } else {
    //             i += 1;
    //         }
    //     }

    //     self.quantify(tyvars)
    // }

    // pub fn unquantify(self) -> Ty {
    //     match self {
    //         Ty::All(_, t) => *t,
    //         t => t,
    //     }
    // }

    // pub fn formalize(self, path: &Path, tyvars: &HashSet<TyVar>) -> (Ty, Subst) {
    //     log::debug!("formalize: {}", self);
    //     let mut subst = Subst::new();
    //     if let Ty::All(xs, _) = &self {
    //         // bind all type variables in the function type
    //         let mut c = 'a' as u8;
    //         for v in xs.iter().filter(|x| !tyvars.contains(x)) {
    //             if !subst.contains_key(v) {
    //                 let path = path.append(format!("'{}", c as char));
    //                 let u = TyVar(path);
    //                 if v == &u {
    //                     continue;
    //                 }

    //                 subst.insert(v.clone(), Ty::Var(u));
    //                 c += 1;
    //             }
    //         }
    //         let ty = self.apply_subst(&subst);
    //         return (ty, subst);
    //     }

    //     (self, subst)
    // }

    // pub fn qualify_in_place(&mut self, preds: &Vec<TyPredicate>) {
    //     log::debug!("qualify in place: {}", self);
    //     let tyvars = self.collect_tyvars();
    //     let ty = std::mem::replace(self, Ty::unit());
    //     *self = ty.qualify(preds, &tyvars);
    // }

    // pub fn qualify(self, preds: &Vec<TyPredicate>, tyvars: &Vec<TyVar>) -> Ty {
    //     log::debug!("preds: {:?}", preds);
    //     log::debug!("tyvars: {:?}", tyvars);
    //     let tyvar_set = tyvars.to_set();
    //     let mut preds = preds
    //         .iter()
    //         .filter_map(|p| {
    //             if !p.collect_tyvars().iter().to_set().is_disjoint(&tyvar_set) {
    //                 Some(p.clone())
    //             } else {
    //                 None
    //             }
    //         })
    //         .collect::<Vec<_>>();

    //     log::debug!("preds: {:?}", preds);
    //     log::debug!("tyvar_set: {:?}", tyvar_set);

    //     preds.sort();
    //     preds.dedup();
    //     self.qualify_with(preds)
    // }

    // fn qualify_with(self, preds: Vec<TyPredicate>) -> Ty {
    //     if preds.len() != 0 {
    //         // wrap the type in a qualified type if there are type variables
    //         match self {
    //             Ty::All(xs, t) => Ty::All(xs, Box::new(t.qualify_with(preds))),
    //             Ty::Qualified(q, t) => {
    //                 log::debug!("prev preds: {:?}", q);
    //                 Ty::Qualified(preds, t)
    //             }
    //             _ => Ty::Qualified(preds, Box::new(self)),
    //         }
    //     } else {
    //         self
    //     }
    // }

    // pub fn unqualify(self) -> Ty {
    //     match self {
    //         Ty::All(xs, t) => Ty::All(xs, Box::new(t.unqualify())),
    //         Ty::Qualified(_, t) => *t,
    //         t => t,
    //     }
    // }

    // pub fn qualifiers(&self) -> Option<&Vec<TyPredicate>> {
    //     match self {
    //         Ty::All(_, t) => t.qualifiers(),
    //         Ty::Qualified(q, _) => Some(q),
    //         _ => None,
    //     }
    // }

    // pub fn has_qualifier(&self, pred: &TyPredicate) -> bool {
    //     match self {
    //         Ty::All(_, ty) => ty.has_qualifier(pred),
    //         Ty::Qualified(preds, _) => preds.contains(pred),
    //         _ => false,
    //     }
    // }

    // pub fn in_hnf(&self) -> bool {
    //     match self {
    //         Ty::Never => todo!(),
    //         Ty::Any => todo!(),
    //         Ty::Var(_) => todo!(),
    //         Ty::Tuple(_) => todo!(),
    //         Ty::Ptr(_) => todo!(),
    //         Ty::Union(_) => todo!(),
    //         Ty::Array(_, _) => todo!(),
    //         Ty::Func(_, _) => todo!(),
    //         Ty::Projection(_, _) => todo!(),
    //         Ty::Qualified(_, _) => todo!(),
    //         Ty::All(_, _) => todo!(),
    //     }
    // }

    pub fn nilable(t: Ty) -> Ty {
        Ty::Union(vec![t, Ty::nil()])
    }

    /// S <: T => S is a subtype of T
    pub fn is_subtype(&self, t: &Ty) -> bool {
        match (self, t) {
            (_, Ty::Any) | (Ty::Never, _) => true,
            (Ty::Tuple(a), Ty::Tuple(b)) => {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.is_subtype(y))
            }
            (Ty::Ptr(a), Ty::Ptr(b)) => a.is_subtype(b),
            (Ty::Projection(a, s), Ty::Projection(b, t)) => {
                a == b && s.len() == t.len() && s.iter().zip(t.iter()).all(|(x, y)| x.is_subtype(y))
            }
            (Ty::Func(r, s), Ty::Func(t, u)) => {
                r.len() == t.len()
                    && r.iter().zip(t.iter()).all(|(x, y)| x.is_subtype(y))
                    && s.is_subtype(u)
            }
            // (Ty::All(xs, s), Ty::All(ys, t)) if xs == ys => s.is_subtype(t),
            _ if self == t => true,
            _ => false,
        }
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, Ty::Tuple(tys) if tys.is_empty())
    }

    pub fn is_nullary(&self) -> bool {
        match self {
            Ty::Never | Ty::Any | Ty::Const(_) | Ty::Union(_) | Ty::Var(_) => true,
            Ty::Projection(_, tys) | Ty::Tuple(tys) => tys.len() == 0,
            Ty::Func(_, _) | Ty::Array(_, _) | Ty::Ptr(_) => false,
        }
    }

    #[inline(always)]
    pub fn is_polymorphic(&self) -> bool {
        !self.free_vars().is_empty()
    }

    // #[inline(always)]
    // pub fn is_forall(&self) -> bool {
    //     matches!(self, Ty::All(..))
    // }

    pub fn is_func(&self) -> bool {
        match &self {
            // Ty::All(_, ty) | Ty::Qualified(_, ty) => ty.is_func(),
            Ty::Func(..) => true,
            _ => false,
        }
    }

    pub fn is_funcs_union(&self) -> bool {
        match &self {
            // Ty::All(_, ty) => ty.is_funcs_union(),
            Ty::Union(tys) => tys.iter().all(|t| t.is_func()),
            _ => false,
        }
    }

    pub fn is_union(&self) -> bool {
        match &self {
            // Ty::All(_, ty) => ty.is_union(),
            Ty::Union(_) => true,
            _ => false,
        }
    }

    pub fn is_tyvar(&self) -> bool {
        matches!(self, Ty::Var(_))
    }

    pub fn is_unknown_tyvar(&self) -> bool {
        matches!(self, Ty::Var(u) if u.is_unknown())
    }

    pub fn as_tyvar(self) -> TyVar {
        match self {
            Ty::Var(v) => v,
            _ => panic!("not a type variable"),
        }
    }

    pub fn get_func_param(&self, idx: usize) -> Option<&Ty> {
        match self {
            Ty::Never
            | Ty::Any
            | Ty::Var(_)
            | Ty::Const(_)
            | Ty::Tuple(_)
            | Ty::Ptr(_)
            | Ty::Union(_)
            | Ty::Array(_, _)
            | Ty::Projection(_, _) => None,
            Ty::Func(params, _) => params.get(idx),
            // Ty::Qualified(_, t) => t.get_func_param(idx),
            // Ty::All(_, t) => t.get_func_param(idx),
        }
    }

    pub fn get_ty_params(&self) -> Vec<&Ty> {
        match self {
            Ty::Array(t, _) | Ty::Ptr(t) => vec![t.as_ref()],
            Ty::Tuple(t) | Ty::Union(t) | Ty::Projection(_, t) => t.iter().collect(),
            Ty::Never | Ty::Any | Ty::Const(_) | Ty::Var(_) | Ty::Func(_, _) => vec![],
        }
    }

    pub fn get_ty_param_at(&self, idx: usize) -> &Ty {
        match self {
            Ty::Array(t, _) => {
                if idx != 0 {
                    panic!("array only has one type parameter: idx={}", idx)
                }

                t.as_ref()
            }
            Ty::Ptr(t) => {
                if idx != 0 {
                    panic!("pointer only has one type parameter: idx={}", idx)
                }

                t.as_ref()
            }
            Ty::Tuple(t) | Ty::Union(t) | Ty::Projection(_, t) => t.iter().nth(idx).unwrap(),
            Ty::Never | Ty::Any | Ty::Const(_) | Ty::Var(_) | Ty::Func(_, _) => {
                panic!("no type parameters: {}", self)
            }
        }
    }

    pub fn set_ty_param_at(&mut self, idx: usize, tp: Ty) {
        match self {
            Ty::Array(t, _) => {
                if idx != 0 {
                    panic!("array only has one type parameter: idx={}", idx)
                }

                *t = Box::new(tp);
            }
            Ty::Ptr(t) => {
                if idx != 0 {
                    panic!("pointer only has one type parameter: idx={}", idx)
                }

                *t = Box::new(tp);
            }
            Ty::Tuple(t) | Ty::Union(t) | Ty::Projection(_, t) => {
                t[idx] = tp;
            }
            Ty::Never | Ty::Any | Ty::Const(_) | Ty::Var(_) | Ty::Func(_, _) => {
                panic!("no type parameters: {}", self)
            }
        }
    }

    #[inline(always)]
    pub fn first_ty_param(&self) -> &Ty {
        self.get_ty_param_at(0)
    }

    pub fn union(&mut self, ty: Ty) {
        log::debug!("union: {} | {}", self, ty);
        match (self, ty) {
            // (Ty::All(xs, t), Ty::All(ys, u)) => {
            //     for y in ys {
            //         if !xs.contains(&y) {
            //             xs.push(y);
            //         }
            //     }
            //     t.union(*u);
            // }
            // (Ty::All(_, t), u) => t.union(u),
            // (t, Ty::All(xs, u)) => replace(t, |mut t| {
            //     t.union(*u);
            //     Ty::All(xs, Box::new(t))
            // }),
            // (Ty::Qualified(p, t), Ty::Qualified(q, u)) => {
            //     p.extend(q);
            //     t.union(*u);
            // }
            // (Ty::Qualified(_, t), u) => {
            //     t.union(u);
            // }
            // (t, Ty::Qualified(p, u)) => replace(t, |mut t| {
            //     t.union(*u);
            //     Ty::Qualified(p, Box::new(t))
            // }),
            (Ty::Union(tys), ty) => {
                if !tys.contains(&ty) {
                    tys.push(ty);
                }
            }
            (ty, Ty::Union(mut tys)) => replace(ty, |t| {
                if !tys.contains(&t) {
                    tys.insert(0, t);
                }
                Ty::Union(tys)
            }),
            (Ty::Func(..), Ty::Func(..)) => {}
            (Ty::Projection(a, x), Ty::Projection(b, y)) if a == &b && x == &y => {}
            (t, u) if t != &u => replace(t, |t| Ty::Union(vec![t, u])),
            _ => {}
        }
    }

    // pub fn add_to_union(&mut self, ty: Ty) {
    //     if let Ty::All(_, t) = self {
    //         t.as_mut().add_to_union(ty);
    //     } else if let Ty::Union(tys) = self {
    //         tys.push(ty);
    //     }
    // }

    // pub fn unpack_quantified_ty(self) -> (Vec<TyVar>, Ty) {
    //     match self {
    //         Ty::All(q, t) => (q, *t),
    //         t => (vec![], t),
    //     }
    // }

    // pub fn unpack_qualified_ty(self) -> (Vec<TyPredicate>, Ty) {
    //     match self {
    //         Ty::All(xs, t) => {
    //             let (q, t) = t.unpack_qualified_ty();
    //             (q, Ty::All(xs, Box::new(t)))
    //         }
    //         Ty::Qualified(q, t) => (q, *t),
    //         t => (vec![], t),
    //     }
    // }

    // pub fn unpack_tuple(self) -> Vec<Ty> {
    //     match self {
    //         Ty::Tuple(tys) => tys,
    //         _ => panic!("not a tuple type"),
    //     }
    // }

    // pub fn try_unpack_overloaded_fn<T: Copy + Clone>(self) -> Result<Vec<Ty>, TypeError> {
    //     if !self.is_func() && !self.is_funcs_union() {
    //         return Err(TypeError::assertion(str!("function"), self));
    //     }

    //     match self {
    //         Ty::Func(p, r) => Ok(vec![Ty::Func(p, r)]),
    //         Ty::All(xs, t) if t.is_func() => Ok(vec![Ty::All(xs, t)]),
    //         Ty::Union(tys) => Ok(tys),
    //         t => unreachable!("attempted to unpack non-function: {:?}", t),
    //     }
    // }

    pub fn try_borrow_fn(&self) -> Result<(&Vec<Ty>, &Ty), TypeError> {
        if !self.is_func() {
            return Err(TypeError::assertion(str!("function"), self.clone()));
        }

        match self {
            Ty::Func(p, r) => Ok((p, r.as_ref())),
            _ => unreachable!("attempted to unpack non-function: {:?}", self),
        }
    }

    pub fn has_ret_placeholder(&self) -> bool {
        self.get_ret_placeholder().is_some()
    }

    pub fn get_ret_placeholder(&self) -> Option<&TyVar> {
        match self {
            Ty::Func(_, ret_ty) => match ret_ty.as_ref() {
                Ty::Var(r) if r.is_ret_placeholder() => Some(r),
                _ => None,
            },
            _ => None,
        }
    }

    // pub fn try_unpack_fn(
    //     self,
    // ) -> Result<(Option<Vec<TyVar>>, Vec<TyPredicate>, Vec<Ty>, Ty), TypeError> {
    //     if !self.is_func() {
    //         return Err(TypeError::assertion(str!("function"), self));
    //     }

    //     match self {
    //         Ty::All(xs, ty) => {
    //             let (_, q, p, r) = ty.try_unpack_fn()?;
    //             Ok((Some(xs), q, p, r))
    //         }
    //         Ty::Qualified(q, ty) => {
    //             let (_, _, p, r) = ty.try_unpack_fn()?;
    //             Ok((None, q, p, r))
    //         }
    //         Ty::Func(p, r) => Ok((None, vec![], p, *r)),
    //         _ => unreachable!("attempted to unpack non-function: {:?}", self),
    //     }
    // }
}

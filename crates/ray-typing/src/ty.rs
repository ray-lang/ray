use std::{
    fmt::Display,
    hash::Hash,
    ops::{BitOr, Deref, DerefMut},
    str::FromStr,
};

use crate::top::{
    Predicate, Predicates, Subst, Substitutable, Ty as TopTy, directives::TypeClassDirective,
};

use ray_shared::{
    collections::{namecontext::NameContext, nametree::Scope},
    pathlib::Path,
    utils::join,
};
use serde::{Deserialize, Serialize};

use ray_shared::span::Source;

use crate::error::TypeError;

use super::{context::TyCtx, info::TypeSystemInfo, traits::QualifyTypes};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TyScheme(crate::top::SchemePredicates<Ty, TyVar>);

impl Deref for TyScheme {
    type Target = crate::top::SchemePredicates<Ty, TyVar>;

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
        Self(crate::top::SchemePredicates::new(
            vars,
            crate::top::Qualification::new(preds, ty),
        ))
    }

    pub fn scheme(scheme: crate::top::SchemePredicates<Ty, TyVar>) -> Self {
        Self(scheme)
    }

    #[inline(always)]
    pub fn from_var(var: TyVar) -> Self {
        Self::from_mono(Ty::Var(var))
    }

    #[inline(always)]
    pub fn from_mono(ty: Ty) -> Self {
        Self(crate::top::SchemePredicates::mono(
            crate::top::Qualification::unqualified(ty),
        ))
    }

    pub fn apply_subst_all(&mut self, subst: &Subst<TyVar, Ty>) {
        self.0.apply_subst_all(subst);
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

    pub fn take(self) -> crate::top::SchemePredicates<Ty, TyVar> {
        self.0
    }

    pub fn try_borrow_fn(&self) -> Option<(&Vec<TyVar>, &Predicates<Ty, TyVar>, &Vec<Ty>, &Ty)> {
        if let Ty::Func(params, ret) = &self.ty.ty {
            Some((&self.vars, &self.ty.qualifiers, params, ret))
        } else {
            None
        }
    }

    pub fn resolve_fqns(&mut self, scopes: &Vec<Scope>, ncx: &NameContext) {
        self.unquantified_mut().ty_mut().resolve_fqns(scopes, ncx)
    }

    pub fn flatten(&self) -> Vec<&Ty> {
        self.ty
            .qualifiers()
            .deref()
            .iter()
            .flat_map(Predicate::flatten)
            .chain(self.ty.ty().flatten().into_iter())
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SigmaTy(crate::top::SigmaPredicates<Ty, TyVar>);

impl Deref for SigmaTy {
    type Target = crate::top::SigmaPredicates<Ty, TyVar>;

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
            crate::top::SigmaPredicates::Var(v) => write!(f, "{}", v),
            crate::top::SigmaPredicates::Scheme(s) => {
                write!(f, "{}", s)
            }
        }
    }
}

impl SigmaTy {
    pub fn var(var: TyVar) -> Self {
        SigmaTy(crate::top::SigmaPredicates::Var(var))
    }

    pub fn scheme(scheme: TyScheme) -> Self {
        SigmaTy(crate::top::SigmaPredicates::Scheme(scheme.take()))
    }

    pub fn mono(ty: Ty) -> Self {
        SigmaTy(crate::top::SigmaPredicates::mono(ty))
    }

    #[inline(always)]
    pub fn is_polymorphic(&self) -> bool {
        self.has_quantifiers()
    }

    pub fn get_mono(&self) -> Option<&Ty> {
        match &self.0 {
            crate::top::SigmaPredicates::Scheme(sch)
                if sch.vars.is_empty() && sch.ty.qualifiers.is_empty() =>
            {
                Some(&sch.ty.ty)
            }
            _ => None,
        }
    }

    pub fn into_mono(self) -> Option<Ty> {
        match self.0 {
            crate::top::SigmaPredicates::Scheme(sch)
                if sch.vars.is_empty() && sch.ty.qualifiers.is_empty() =>
            {
                Some(sch.ty.ty)
            }
            _ => None,
        }
    }

    pub fn get_mono_mut(&mut self) -> Option<&mut Ty> {
        match &mut self.0 {
            crate::top::SigmaPredicates::Scheme(sch)
                if sch.vars.is_empty() && sch.ty.qualifiers.is_empty() =>
            {
                Some(&mut sch.ty.ty)
            }
            _ => None,
        }
    }

    pub fn get_scheme(&self) -> Option<&crate::top::SchemePredicates<Ty, TyVar>> {
        match &self.0 {
            crate::top::SigmaPredicates::Scheme(sch) => Some(sch),
            _ => None,
        }
    }

    pub fn get_scheme_mut(&mut self) -> Option<&mut crate::top::SchemePredicates<Ty, TyVar>> {
        match &mut self.0 {
            crate::top::SigmaPredicates::Scheme(sch) => Some(sch),
            _ => None,
        }
    }

    pub fn has_quantifiers(&self) -> bool {
        match &self.0 {
            crate::top::SigmaPredicates::Scheme(sch) => !sch.vars.is_empty(),
            _ => false,
        }
    }

    pub fn quantifiers(&self) -> Option<&Vec<TyVar>> {
        match &self.0 {
            crate::top::Sigma::Scheme(sch) => Some(sch.quantifiers()),
            _ => None,
        }
    }

    pub fn take(self) -> crate::top::SigmaPredicates<Ty, TyVar> {
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

impl crate::top::TyVar for TyVar {
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

    fn is_meta(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            return name.starts_with("?t");
        }

        false
    }

    fn is_schema(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            return name.starts_with("?s");
        }

        false
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
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NominalKind {
    Struct,
}

impl Display for NominalKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NominalKind::Struct => write!(f, "struct"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StructTy {
    pub kind: NominalKind,
    pub path: Path,
    pub ty: TyScheme,
    pub fields: Vec<(String, TyScheme)>,
}

impl Display for StructTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {{", self.path)?;

        for (i, (field, ty)) in self.fields.iter().enumerate() {
            write!(f, " {}: {}", field, ty)?;
            if i < self.fields.len() - 1 {
                write!(f, ", ")?;
            } else {
                write!(f, " ")?;
            }
        }
        write!(f, "}}")?;
        Ok(())
    }
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

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverMode {
    #[default]
    None,
    Value,
    Ptr,
}

impl ReceiverMode {
    pub fn from_signature(param_tys: &[Ty], is_static: bool) -> Self {
        if is_static || param_tys.is_empty() {
            return ReceiverMode::None;
        }

        // First parameter is always considered the receiver for non-static methods.
        // If it is a pointer type, we treat the method as a pointer receiver,
        // otherwise as a value receiver.
        match &param_tys[0] {
            Ty::Ref(_) => ReceiverMode::Ptr,
            _ => ReceiverMode::Value,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldKind {
    Method,
}

impl std::fmt::Display for FieldKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FieldKind::Method => write!(f, "method"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraitField {
    pub kind: FieldKind,
    pub name: String,
    pub ty: TyScheme,
    pub is_static: bool,
    pub recv_mode: ReceiverMode,
}

impl TraitField {
    pub fn receiver_ty(&self) -> Option<&Ty> {
        let Some((_, _, param_tys, _)) = self.ty.try_borrow_fn() else {
            return None;
        };

        if param_tys.is_empty() {
            return None;
        }

        Some(&param_tys[0])
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraitTy {
    pub path: Path,
    pub ty: Ty,
    pub super_traits: Vec<Ty>,
    pub fields: Vec<TraitField>,
    pub directives: Vec<TypeClassDirective<TypeSystemInfo, Ty, TyVar>>,
}

impl TraitTy {
    pub fn field_tys(&self) -> Vec<TyScheme> {
        self.fields.iter().map(|f| f.ty.clone()).collect()
    }

    pub fn create_method_path(&self, method_name: &str, receiver_ty: Option<&Ty>) -> Path {
        let mut method_path = self.path.clone();
        let type_params = self.ty.get_ty_params();
        if !type_params.is_empty() {
            let mut type_args = type_params
                .iter()
                .map(|ty| ty.to_string())
                .collect::<Vec<_>>();
            if let Some(receiver_ty) = receiver_ty {
                if !type_args.is_empty() {
                    type_args[0] = receiver_ty.to_string();
                }
            }
            method_path = method_path.append_type_args(type_args.iter());
        }

        log::debug!(
            "[resolve_trait_method] trait_path={} type_params={:?} produced={}",
            self.path,
            type_params
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>(),
            method_path.append(method_name.to_string())
        );
        method_path.append(method_name.to_string())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImplField {
    pub kind: FieldKind,
    pub path: Path,
    pub scheme: Option<TyScheme>,
    pub src: Source,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImplTy {
    pub base_ty: Ty,
    pub trait_ty: Ty,
    pub ty_args: Vec<Ty>,
    pub predicates: Vec<Predicate<Ty, TyVar>>,
    pub fields: Vec<ImplField>,
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
    Ref(Box<Ty>),
    RawPtr(Box<Ty>),
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
            Ty::Ref(ty) => {
                write!(f, "*{}", ty)
            }
            Ty::RawPtr(ty) => {
                write!(f, "rawptr[{}]", ty)
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
            Ty::Ref(ty) | Ty::RawPtr(ty) | Ty::Array(ty, _) => {
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
            Ty::Ref(ty) | Ty::RawPtr(ty) | Ty::Array(ty, _) => {
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
            Ty::Ref(ty) | Ty::RawPtr(ty) | Ty::Array(ty, _) => ty.free_vars(),
            Ty::Func(param_tys, ret_ty) => {
                let mut vars = param_tys.free_vars();
                vars.extend(ret_ty.free_vars());
                vars
            }
        }
    }
}

impl crate::top::Ty<TyVar> for Ty {
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

    fn ptr(ty: Self) -> Self {
        Ty::Ref(Box::new(ty))
    }

    fn maybe_var(&self) -> Option<&TyVar> {
        match self {
            Ty::Var(v) => Some(v),
            _ => None,
        }
    }

    fn maybe_const(&self) -> Option<&str> {
        match self {
            Ty::Any => Some("any"),
            Ty::Never => Some("never"),
            Ty::Const(n) => Some(n),
            _ => None,
        }
    }

    fn maybe_app(&self) -> Option<(Self, Vec<Self>)> {
        match self {
            Ty::Array(ty, size) => {
                Some((Ty::Const(format!("[{}]", size)), vec![ty.as_ref().clone()]))
            }
            Ty::Projection(n, tys) => Some((n.as_ref().clone(), tys.clone())),
            Ty::Ref(ty) => Some((Ty::Const(str!("*")), vec![ty.as_ref().clone()])),
            Ty::RawPtr(ty) => Some((Ty::Const(str!("rawptr")), vec![ty.as_ref().clone()])),
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

    fn maybe_union(&self) -> Option<&Vec<Self>> {
        match self {
            Ty::Union(tys) => Some(tys),
            _ => None,
        }
    }

    fn maybe_ptr(&self) -> Option<&Self> {
        match self {
            Ty::Ref(ptee) => Some(&ptee),
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
            Ty::Array(ty, _) | Ty::Ref(ty) | Ty::RawPtr(ty) | Ty::Projection(ty, _) => {
                ty.in_head_normal_form()
            }
        }
    }

    fn name(&self) -> &str {
        match self {
            Ty::Never => "never",
            Ty::Any => "any",
            Ty::Var(_) => todo!(),
            Ty::Tuple(_) => todo!(),
            Ty::Ref(_) => todo!(),
            Ty::RawPtr(_) => todo!(),
            Ty::Union(_) => todo!(),
            Ty::Array(_, _) => todo!(),
            Ty::Func(_, _) => todo!(),
            Ty::Const(n) => n,
            Ty::Projection(ty, _) => crate::top::Ty::name(ty.as_ref()),
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
            Ty::Ref(ty) | Ty::RawPtr(ty) | Ty::Array(ty, _) => ty.variables(),
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
            Ty::Ref(ty) | Ty::RawPtr(ty) | Ty::Array(ty, _) => ty.constants(),
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
        _: &Self,
        _: &crate::top::OrderedTypeSynonyms<Self, TyVar>,
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
            Ty::Ref(ty) => Ty::Ref(Box::new(ty.freeze_vars())),
            Ty::RawPtr(ty) => Ty::RawPtr(Box::new(ty.freeze_vars())),
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
            Ty::Ref(ty) => Ty::Ref(Box::new(ty.unfreeze_vars())),
            Ty::RawPtr(ty) => Ty::RawPtr(Box::new(ty.unfreeze_vars())),
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

    fn flatten(&self) -> Vec<&Ty> {
        match self {
            Ty::Never | Ty::Any | Ty::Var(_) | Ty::Const(_) => vec![self],
            Ty::Tuple(items) | Ty::Union(items) => items.iter().flat_map(Ty::flatten).collect(),
            Ty::Ref(ty) | Ty::RawPtr(ty) | Ty::Array(ty, _) => ty.flatten(),
            Ty::Func(items, ty) => items
                .iter()
                .chain(std::iter::once(ty.as_ref()))
                .flat_map(Ty::flatten)
                .collect(),
            Ty::Projection(ty, items) => std::iter::once(ty.as_ref())
                .chain(items.iter())
                .flat_map(Ty::flatten)
                .collect(),
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
            "list" => Ty::list(Ty::Never),
            "range" => Ty::range(Ty::Never),
            "rawptr" => Ty::raw_ptr(Ty::Never),
            _ => return None,
        })
    }

    pub fn desc(&self) -> String {
        match self {
            Ty::Never => str!("never"),
            Ty::Any => str!("any"),
            Ty::Var(_) => str!("variable"),
            Ty::Tuple(_) => str!("tuple"),
            Ty::Ref(ty) => format!("reference to {}", ty.desc()),
            Ty::RawPtr(ty) => format!("raw pointer to {}", ty.desc()),
            Ty::Union(_) => str!("union"),
            Ty::Array(ty, _) => format!("array of {}", ty.desc()),
            Ty::Func(_, _) => str!("function"),
            Ty::Const(name) => name.clone(),
            Ty::Projection(ty, _) => ty.desc(),
        }
    }

    pub fn resolve_fqns(&mut self, scopes: &Vec<Scope>, ncx: &NameContext) {
        match self {
            Ty::Const(name) => {
                if Ty::is_builtin_name(name) {
                    return;
                }

                if let Some(fqn) = ncx.resolve_name(scopes, name) {
                    log::debug!("[resolve_fqns] resolved name: {} -> {:?}", name, fqn);
                    *name = fqn.to_string();
                } else {
                    log::debug!(
                        "[resolve_fqns] COULD NOT RESOLVE NAME {} in scopes = {:?}",
                        name,
                        scopes
                    )
                }
            }
            Ty::Projection(ty, tys) => {
                ty.resolve_fqns(scopes, ncx);
                for ty in tys {
                    ty.resolve_fqns(scopes, ncx);
                }
            }
            Ty::Tuple(tys) | Ty::Union(tys) => {
                tys.iter_mut().for_each(|t| t.resolve_fqns(scopes, ncx));
            }
            Ty::Ref(t) | Ty::RawPtr(t) | Ty::Array(t, _) => t.resolve_fqns(scopes, ncx),
            Ty::Func(params, ret) => {
                params.iter_mut().for_each(|t| t.resolve_fqns(scopes, ncx));
                ret.resolve_fqns(scopes, ncx);
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
                    let mapped_tv = tcx.tf().next_with_prefix("?s");
                    tcx.add_var_mapping(tv.clone(), mapped_tv.clone());
                    tcx.add_schema_var(mapped_tv.clone());
                    mapped_tv
                };
            }
            Ty::Tuple(tys) | Ty::Union(tys) => {
                tys.iter_mut().for_each(|t| t.map_vars(tcx));
            }
            Ty::Projection(ty, param_tys) => {
                ty.map_vars(tcx);
                param_tys.iter_mut().for_each(|t| t.map_vars(tcx));
            }
            Ty::Array(ty, _) | Ty::Ref(ty) | Ty::RawPtr(ty) => ty.map_vars(tcx),
            Ty::Func(param_tys, ret_ty) => {
                param_tys.iter_mut().for_each(|t| t.map_vars(tcx));
                ret_ty.map_vars(tcx);
            }
        }
    }

    pub fn is_builtin_name(name: &str) -> bool {
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
    pub fn proj(ty: Ty, params: Vec<Ty>) -> Ty {
        Ty::Projection(Box::new(ty), params)
    }

    #[inline(always)]
    pub fn refty(ty: Ty) -> Ty {
        Ty::Ref(Box::new(ty))
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
    pub fn raw_ptr(el: Ty) -> Ty {
        Ty::RawPtr(Box::new(el))
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
    pub fn is_builtin(&self) -> bool {
        match self {
            Ty::Const(name) => Ty::is_builtin_name(name),
            _ => false,
        }
    }

    #[inline(always)]
    pub fn is_meta_ty(&self) -> bool {
        match self {
            Ty::Projection(inner, _) => match inner.as_ref() {
                Ty::Const(fqn) => fqn == "type",
                _ => false,
            },
            _ => false,
        }
    }

    #[inline(always)]
    pub fn get_path(&self) -> Path {
        match self {
            Ty::Never => Path::from("never"),
            Ty::Any => Path::from("any"),
            Ty::Var(v) => v.path().clone(),
            Ty::Const(s) => Path::from(s.clone()),
            Ty::Projection(ty, params) => {
                let base_path = ty.get_path();
                base_path.append_type_args(params.iter())
            }
            Ty::Array(ty, size) => {
                let base_path = Path::from("array");
                let args = &[ty.to_string(), size.to_string()];
                base_path.append_type_args(args.iter())
            }
            Ty::Ref(ty) => {
                let base_path = Path::from("ref");
                base_path.append_type_args(std::iter::once(ty))
            }
            Ty::RawPtr(ty) => {
                let base_path = Path::from("rawptr");
                base_path.append_type_args(std::iter::once(ty))
            }
            Ty::Tuple(tys) => {
                let base_path = Path::from("tuple");
                base_path.append_type_args(tys.iter())
            }
            Ty::Union(_) | Ty::Func(_, _) => {
                unimplemented!()
            }
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
            Ty::Array(..) | Ty::Ref(_) | Ty::RawPtr(_) | Ty::Union(_) | Ty::Func(_, _) => {
                str!("")
            }
        }
    }

    pub fn nilable(t: Ty) -> Ty {
        Ty::Union(vec![t, Ty::con("nil")])
    }

    /// S <: T => S is a subtype of T
    pub fn is_subtype(&self, t: &Ty) -> bool {
        match (self, t) {
            (_, Ty::Any) | (Ty::Never, _) => true,
            (Ty::Tuple(a), Ty::Tuple(b)) => {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.is_subtype(y))
            }
            (Ty::Ref(a), Ty::Ref(b)) => a.is_subtype(b),
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
            Ty::Func(_, _) | Ty::Array(_, _) | Ty::Ref(_) | Ty::RawPtr(_) => false,
        }
    }

    #[inline(always)]
    pub fn is_polymorphic(&self) -> bool {
        !self.free_vars().is_empty()
    }

    pub fn is_func(&self) -> bool {
        match &self {
            Ty::Func(..) => true,
            _ => false,
        }
    }

    pub fn is_funcs_union(&self) -> bool {
        match &self {
            Ty::Union(tys) => tys.iter().all(|t| t.is_func()),
            _ => false,
        }
    }

    pub fn is_union(&self) -> bool {
        match &self {
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

    pub fn is_aggregate(&self) -> bool {
        match self {
            Ty::Const(fqn) => match fqn.as_str() {
                "bool" | "i8" | "u8" | "i16" | "u16" | "i32" | "u32" | "char" | "u64" | "i64"
                | "int" | "uint" => false,
                _ => true,
            },
            Ty::Projection(inner, _) => inner.is_aggregate(),
            Ty::Tuple(tys) => tys.len() > 0,
            Ty::Array(_, _) => true,
            Ty::Never
            | Ty::Any
            | Ty::Var(_)
            | Ty::Ref(_)
            | Ty::RawPtr(_)
            | Ty::Func(_, _)
            | Ty::Union(_) => false,
        }
    }

    pub fn nominal_kind(&self, tcx: &TyCtx) -> Option<NominalKind> {
        let fqn = self.get_path();
        tcx.get_struct_ty(&fqn).map(|s| s.kind)
    }

    pub fn is_struct(&self, tcx: &TyCtx) -> bool {
        self.nominal_kind(tcx) == Some(NominalKind::Struct)
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
            | Ty::Ref(_)
            | Ty::RawPtr(_)
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
            Ty::Array(t, _) | Ty::Ref(t) | Ty::RawPtr(t) => vec![t.as_ref()],
            Ty::Tuple(t) | Ty::Union(t) | Ty::Projection(_, t) => t.iter().collect(),
            Ty::Never | Ty::Any | Ty::Const(_) | Ty::Var(_) | Ty::Func(_, _) => vec![],
        }
    }

    pub fn get_ty_param_at(&self, idx: usize) -> Option<&Ty> {
        match self {
            Ty::Array(t, _) => {
                if idx != 0 {
                    panic!("array only has one type parameter: idx={}", idx)
                }

                Some(t.as_ref())
            }
            Ty::Ref(t) => {
                if idx != 0 {
                    panic!("reference only has one type parameter: idx={}", idx)
                }

                Some(t.as_ref())
            }
            Ty::RawPtr(t) => {
                if idx != 0 {
                    panic!("rawptr only has one type parameter: idx={}", idx)
                }

                Some(t.as_ref())
            }
            Ty::Tuple(t) | Ty::Union(t) | Ty::Projection(_, t) => Some(t.iter().nth(idx).unwrap()),
            Ty::Never | Ty::Any | Ty::Const(_) | Ty::Var(_) | Ty::Func(_, _) => None,
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
            Ty::Ref(t) => {
                if idx != 0 {
                    panic!("reference only has one type parameter: idx={}", idx)
                }

                *t = Box::new(tp);
            }
            Ty::RawPtr(t) => {
                if idx != 0 {
                    panic!("rawptr only has one type parameter: idx={}", idx)
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
        self.get_ty_param_at(0).unwrap()
    }

    pub fn union(&mut self, ty: Ty) {
        log::debug!("union: {} | {}", self, ty);
        match (self, ty) {
            (Ty::Union(tys), ty) => {
                if !tys.contains(&ty) {
                    tys.push(ty);
                }
            }
            (ty, Ty::Union(mut tys)) => {
                let prev = ty.clone();
                *ty = {
                    if !tys.contains(&prev) {
                        tys.insert(0, prev);
                    }
                    Ty::Union(tys)
                };
            }
            (Ty::Func(..), Ty::Func(..)) => {}
            (Ty::Projection(a, x), Ty::Projection(b, y)) if a == &b && x == &y => {}
            (t, u) if t != &u => {
                let prev_t = t.clone();
                *t = Ty::Union(vec![prev_t, u])
            }
            _ => {}
        }
    }

    pub fn try_borrow_fn(&self) -> Result<(&Vec<Ty>, &Ty), TypeError> {
        if !self.is_func() {
            return Err(TypeError::assertion(str!("function"), self.clone()));
        }

        match self {
            Ty::Func(p, r) => Ok((p, r.as_ref())),
            _ => unreachable!("attempted to unpack non-function: {:?}", self),
        }
    }

    pub fn get_fn_ret_ty(&self) -> Option<&Ty> {
        match self {
            Ty::Func(_, ty) => Some(ty.as_ref()),
            _ => None,
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

    pub fn unwrap_pointer(&self) -> Option<&Ty> {
        match self {
            Ty::Ref(inner) | Ty::RawPtr(inner) => Some(&inner),
            _ => None,
        }
    }

    #[inline]
    pub fn is_any_pointer(&self) -> bool {
        matches!(self, Ty::Ref(_) | Ty::RawPtr(_))
    }
}

#[cfg(test)]
mod tests {
    use crate::top::Ty as _;

    use super::Ty;

    #[test]
    fn flattens() {
        // b => b
        let b = Ty::bool();
        assert_eq!(b.flatten(), vec![&b]);

        // (p0, p1) -> r => [p0, p1, r]
        let p0 = Ty::i32();
        let p1 = Ty::string();
        let param_tys = vec![p0.clone(), p1.clone()];
        let ret_ty = Ty::float();
        let f = Ty::Func(param_tys, Box::new(ret_ty.clone()));
        assert_eq!(f.flatten(), vec![&p0, &p1, &ret_ty]);

        // A[T, U] => [A, T, U]
        let base = Ty::con("A");
        let t = Ty::var("T");
        let u = Ty::var("U");
        let a = Ty::proj(base.clone(), vec![t.clone(), u.clone()]);
        assert_eq!(a.flatten(), vec![&base, &t, &u]);

        // B[V, A[T, U]] => [B, V, A, T, U]
        let base_b = Ty::con("B");
        let base_a = Ty::con("A");
        let t = Ty::var("T");
        let u = Ty::var("U");
        let v = Ty::var("V");
        let a = Ty::proj(base_a.clone(), vec![t.clone(), u.clone()]);
        let b = Ty::proj(base_b.clone(), vec![v.clone(), a.clone()]);
        assert_eq!(b.flatten(), vec![&base_b, &v, &base_a, &t, &u]);
    }
}

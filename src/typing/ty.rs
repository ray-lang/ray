use std::{
    collections::{HashMap, HashSet},
    ops::BitOr,
};

use crate::{
    ast::{self, FnSig, HasSource, Path},
    convert::ToSet,
    errors::{RayError, RayErrorKind},
    lir::Size,
    pathlib::FilePath,
    span::{Source, SourceMap, Span},
    utils::{join, replace},
};

use super::{
    context::TyCtx,
    predicate::TyPredicate,
    state::TyVarFactory,
    subst::{ApplySubst, Subst},
    traits::{CollectTyVars, Generalize, HasFreeVars, Instantiate, Polymorphize, Skolemize},
    InferError,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl ApplySubst for TyVar {
    fn apply_subst(self, subst: &Subst) -> TyVar {
        subst.get_var(self)
    }
}

impl Polymorphize for TyVar {
    fn polymorphize(self, tf: &mut TyVarFactory, subst: &mut HashMap<Ty, TyVar>) -> Self {
        if let Some(tv) = subst.get(&Ty::Var(self.clone())) {
            tv.clone()
        } else {
            let path = self.path().parent();
            let tv = tf.with_scope(&path);
            subst.insert(Ty::Var(self), tv.clone());
            tv
        }
    }
}

impl TyVar {
    pub fn path(&self) -> &Path {
        &self.0
    }

    pub fn path_mut(&mut self) -> &mut Path {
        &mut self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StructTy {
    pub path: ast::Path,
    pub ty: Ty,
    pub fields: Vec<(String, Ty)>,
}

impl StructTy {
    pub fn get_field(&self, f: &String) -> Option<(usize, &Ty)> {
        self.fields
            .iter()
            .enumerate()
            .find_map(|(idx, (g, t))| if f == g { Some((idx, t)) } else { None })
    }

    pub fn field_tys(&self) -> Vec<Ty> {
        self.fields.iter().map(|(_, t)| t.clone()).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraitTy {
    pub path: ast::Path,
    pub ty: Ty,
    pub super_traits: Vec<Ty>,
    pub fields: Vec<(String, Ty)>,
}

impl TraitTy {
    pub fn field_tys(&self) -> Vec<Ty> {
        self.fields.iter().map(|(_, t)| t.clone()).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ImplTy {
    pub base_ty: Ty,
    pub trait_ty: Ty,
    pub predicates: Vec<TyPredicate>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Ty {
    Never,
    Any,
    Var(TyVar),
    Tuple(Vec<Ty>),
    Ptr(Box<Ty>),
    Union(Vec<Ty>),
    Array(Box<Ty>, usize),
    Func(Vec<Ty>, Box<Ty>),
    Projection(String, Vec<Ty>),
    Cast(Box<Ty>, Box<Ty>),
    Qualified(Vec<TyPredicate>, Box<Ty>),
    All(Vec<TyVar>, Box<Ty>),
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
            Ty::Projection(n, t) => {
                if t.len() != 0 {
                    write!(f, "{}[{}]", n, join(t, ", "))
                } else {
                    write!(f, "{}", n)
                }
            }
            Ty::Cast(from, to) => write!(f, "cast({}, {})", from, to),
            Ty::Qualified(qual, t) => {
                let q = if qual.len() != 0 {
                    format!(" where {}", join(qual, ", "))
                } else {
                    str!("")
                };
                write!(f, "{}{}", t, q)
            }
            Ty::All(xs, t) => write!(f, "All[{}]{}", join(xs, ", "), t),
        }
    }
}

impl Default for Ty {
    fn default() -> Ty {
        Ty::unit()
    }
}

impl ApplySubst for Ty {
    fn apply_subst(self, subst: &Subst) -> Ty {
        match self {
            any @ Ty::Any => any,
            never @ Ty::Never => never,
            Ty::Var(v) => subst.get_ty_for_var(&v),
            Ty::Tuple(tys) => Ty::Tuple(tys.apply_subst(subst)),
            Ty::Array(ty, size) => Ty::Array(ty.apply_subst(subst), size),
            Ty::Ptr(ty) => Ty::Ptr(ty.apply_subst(subst)),
            Ty::Union(tys) => {
                let mut tys = tys.apply_subst(subst);
                let mut i = 0;
                while i < tys.len() {
                    let mut j = i + 1;
                    while j < tys.len() {
                        if &tys[i] == &tys[j] {
                            tys.remove(j);
                        } else {
                            j += 1;
                        }
                    }
                    i += 1;
                }

                if tys.len() == 1 {
                    tys.pop().unwrap()
                } else {
                    Ty::Union(tys)
                }
            }
            Ty::Func(a, r) => Ty::Func(a.apply_subst(subst), r.apply_subst(subst)),
            Ty::Projection(n, t) => Ty::Projection(n, t.apply_subst(subst)),
            Ty::Cast(f, t) => Ty::Cast(f.apply_subst(subst), t.apply_subst(subst)),
            Ty::Qualified(p, ty) => {
                let mut preds = p.apply_subst(subst);
                preds.sort();
                preds.dedup();
                let ty = ty.apply_subst(subst);
                let preds_freevars = preds.collect_tyvars().to_set();
                let ty_freevars = ty.collect_tyvars().to_set();
                if preds_freevars.is_disjoint(&ty_freevars) {
                    *ty
                } else {
                    Ty::Qualified(preds, ty)
                }
            }
            Ty::All(xs, ty) => {
                let ty = ty.apply_subst(subst);
                let freevars = ty.collect_tyvars().to_set();
                let xs = xs
                    .apply_subst(subst)
                    .into_iter()
                    .filter(|x| freevars.contains(x))
                    .collect::<Vec<_>>();
                if xs.len() == 0 {
                    *ty
                } else {
                    Ty::All(xs, ty)
                }
            }
        }
    }
}

impl Generalize for Ty {
    fn generalize(self, m: &Vec<Ty>, preds: &Vec<TyPredicate>) -> Ty {
        // generalize(M, τ) => ∀{a}.τ where {a} = ftv(τ) − ftv(M).
        let freevars = m.free_vars();
        let mut tyvars = self.collect_tyvars();
        let mut i = 0;
        while i < tyvars.len() {
            let t = &tyvars[i];
            if freevars.contains(&t) {
                tyvars.remove(i);
            } else {
                i += 1;
            }
        }

        self.qualify(preds, &tyvars).quantify(tyvars)
    }
}

impl Generalize for Vec<Ty> {
    fn generalize(self, m: &Vec<Ty>, preds: &Vec<TyPredicate>) -> Self {
        self.into_iter().map(|t| t.generalize(m, &preds)).collect()
    }
}

impl HasFreeVars for Ty {
    fn free_vars(&self) -> HashSet<&TyVar> {
        match self {
            Ty::All(xs, _) => xs.iter().collect(),
            Ty::Union(tys) => tys.free_vars(),
            Ty::Projection(..)
            | Ty::Array(..)
            | Ty::Tuple(..)
            | Ty::Func(..)
            | Ty::Qualified(..)
            | Ty::Cast(..)
            | Ty::Ptr(_)
            | Ty::Var(_)
            | Ty::Never
            | Ty::Any => HashSet::new(),
        }
    }
}

impl CollectTyVars for Ty {
    fn collect_tyvars(&self) -> Vec<TyVar> {
        let mut vs = match self {
            Ty::All(_, t) | Ty::Qualified(_, t) | Ty::Ptr(t) | Ty::Array(t, _) => {
                t.collect_tyvars()
            }
            Ty::Func(param_tys, ret) => param_tys
                .iter()
                .chain(std::iter::once(ret.as_ref()))
                .flat_map(|t| t.collect_tyvars())
                .collect(),
            Ty::Var(v) => vec![v.clone()].into_iter().collect(),
            Ty::Tuple(t) | Ty::Union(t) | Ty::Projection(_, t) => {
                t.iter().flat_map(|t| t.collect_tyvars()).collect()
            }
            Ty::Cast(src, dst) => {
                let mut ty_vars = src.collect_tyvars();
                ty_vars.extend(dst.collect_tyvars());
                ty_vars
            }
            Ty::Never | Ty::Any => vec![],
        };

        vs.sort();
        vs.dedup();
        vs
    }
}

impl Polymorphize for Ty {
    fn polymorphize(self, tf: &mut TyVarFactory, subst: &mut HashMap<Ty, TyVar>) -> Ty {
        if let Some(tv) = subst.get(&self) {
            return Ty::Var(tv.clone());
        }

        match self {
            Ty::Never => Ty::Never,
            Ty::Any => Ty::Any,
            Ty::Var(t) => Ty::Var(t.polymorphize(tf, subst)),
            Ty::Tuple(tys) => Ty::Tuple(tys.polymorphize(tf, subst)),
            Ty::Union(tys) => Ty::Union(tys.polymorphize(tf, subst)),
            Ty::Func(p, r) => Ty::Func(p.polymorphize(tf, subst), r.polymorphize(tf, subst)),
            Ty::Array(t, size) => Ty::Array(t.polymorphize(tf, subst), size),
            Ty::Ptr(t) => Ty::Ptr(t.polymorphize(tf, subst)),
            proj @ Ty::Projection(..) => {
                let tv = tf.next();
                subst.insert(proj, tv.clone());
                Ty::Var(tv)
            }
            Ty::Cast(src, dst) => {
                Ty::Cast(src.polymorphize(tf, subst), dst.polymorphize(tf, subst))
            }
            Ty::Qualified(preds, t) => {
                Ty::Qualified(preds.polymorphize(tf, subst), t.polymorphize(tf, subst))
            }
            Ty::All(xs, t) => Ty::All(xs.polymorphize(tf, subst), t.polymorphize(tf, subst)),
        }
    }
}

impl Instantiate for Ty {
    fn instantiate(self, tf: &mut TyVarFactory) -> Ty {
        match self {
            Ty::Var(v) => Ty::Var(v),
            Ty::Union(tys) => Ty::Union(tys.instantiate(tf)),
            Ty::Tuple(tys) => Ty::Tuple(tys.instantiate(tf)),
            Ty::Func(p, r) => Ty::Func(p.instantiate(tf), r.instantiate(tf)),
            Ty::Cast(src, dst) => Ty::Cast(src.instantiate(tf), dst.instantiate(tf)),
            Ty::Ptr(t) => Ty::Ptr(t.instantiate(tf)),
            Ty::Array(t, size) => Ty::Array(t.instantiate(tf), size),
            Ty::Projection(s, tys) => Ty::Projection(s, tys.instantiate(tf)),
            Ty::Qualified(p, t) => Ty::Qualified(p.instantiate(tf), t.instantiate(tf)),
            Ty::All(xs, t) => {
                let new_xs = (0..xs.len()).into_iter().map(|_| Ty::Var(tf.next()));
                let sub = Subst::from_types(xs, new_xs);
                (*t).apply_subst(&sub)
            }
            t @ Ty::Never | t @ Ty::Any => t,
        }
    }
}

impl<T> Instantiate for Vec<T>
where
    T: Instantiate,
{
    fn instantiate(self, tf: &mut TyVarFactory) -> Vec<T> {
        self.into_iter().map(|t| t.instantiate(tf)).collect()
    }
}

impl Skolemize for Ty {
    fn skolemize(&self, sf: &mut TyVarFactory) -> (Self, Vec<TyVar>)
    where
        Self: Sized,
    {
        let ty = self.clone();
        let prev_vars = ty.collect_tyvars();
        let ty = ty.instantiate(sf).generalize(&vec![], &vec![]);
        let mut vars = ty.collect_tyvars();
        for v in prev_vars {
            if let Some(pos) = vars.iter().position(|x| x == &v) {
                vars.remove(pos);
            }
        }
        (ty, vars)
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

impl Ty {
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

    pub fn from_sig(
        sig: &FnSig,
        fn_scope: &Path,
        filepath: &FilePath,
        fn_tcx: &mut TyCtx,
        parent_tcx: &mut TyCtx,
        srcmap: &SourceMap,
    ) -> Result<Ty, RayError> {
        let mut param_tys = vec![];

        for param in sig.params.iter() {
            if let Some(ty) = param.ty() {
                let mut ty = ty.clone();
                ty.resolve_ty(&fn_scope, fn_tcx);
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

        let mut ret_ty = sig.ret_ty.as_deref().cloned().unwrap_or_default();
        ret_ty.resolve_ty(&fn_scope, fn_tcx);

        let mut ty = Ty::Func(param_tys, Box::new(ret_ty));

        if sig.qualifiers.len() != 0 {
            let mut p = vec![];
            for q in sig.qualifiers.iter() {
                p.push(TyPredicate::from_ast_ty(q, &fn_scope, &filepath, fn_tcx)?);
            }
            ty = Ty::Qualified(p, Box::new(ty));
        }

        let free_vars = parent_tcx.free_vars();
        let ty_vars = ty
            .collect_tyvars()
            .into_iter()
            .filter(|tv| !free_vars.contains(tv))
            .collect::<Vec<_>>();

        Ok(if ty_vars.len() != 0 {
            Ty::All(ty_vars, Box::new(ty))
        } else {
            ty
        })
    }

    pub fn resolve_ty(&mut self, scope: &ast::Path, tcx: &mut TyCtx) {
        match self {
            Ty::Projection(name, ty_params) => {
                ty_params.iter_mut().for_each(|t| t.resolve_ty(scope, tcx));

                if let Some(fqn) = tcx.lookup_fqn(name) {
                    *name = fqn.to_string();
                    return;
                }

                if let Some(ty) = tcx.get_var(&name) {
                    let _ = std::mem::replace(self, ty.clone());
                }
            }
            Ty::Var(tv) => {
                let fqn = scope.append(format!("'{}", tv));
                let fqn_string = fqn.to_string();
                if let Some(ty) = tcx.get_var(&fqn_string) {
                    let _ = std::mem::replace(self, ty.clone());
                } else {
                    *tv.path_mut() = fqn;
                    tcx.bind_var(fqn_string, self.clone());
                }
            }
            Ty::Tuple(tys) | Ty::Union(tys) => {
                tys.iter_mut().for_each(|t| t.resolve_ty(scope, tcx));
            }
            Ty::Ptr(t) | Ty::Array(t, _) => t.resolve_ty(scope, tcx),
            Ty::Func(params, ret) => {
                params.iter_mut().for_each(|t| t.resolve_ty(scope, tcx));
                ret.resolve_ty(scope, tcx);
            }
            Ty::Cast(s, t) => {
                s.resolve_ty(scope, tcx);
                t.resolve_ty(scope, tcx);
            }
            Ty::Qualified(qs, t) => t.resolve_ty(scope, tcx),
            Ty::All(xs, t) => t.resolve_ty(scope, tcx),
            Ty::Never | Ty::Any => {}
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
    pub fn con<S: Into<String>>(s: S) -> Ty {
        Ty::Projection(s.into(), vec![])
    }

    #[inline(always)]
    pub fn ptr(ty: Ty) -> Ty {
        Ty::Ptr(Box::new(ty))
    }

    #[inline(always)]
    pub fn ty_type(ty: Ty) -> Ty {
        Ty::Projection(str!("type"), vec![ty])
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
        Ty::Projection(str!("string"), vec![])
    }

    #[inline(always)]
    pub fn bytes() -> Ty {
        Ty::con("bytes")
    }

    #[inline(always)]
    pub fn range(el: Ty) -> Ty {
        Ty::Projection(str!("range"), vec![el.clone()])
    }

    #[inline(always)]
    pub fn list(el: Ty) -> Ty {
        Ty::Projection(str!("list"), vec![el])
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
            Ty::Projection(a, _)
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
            Ty::Projection(a, _) if matches!(a.as_str(), "float" | "f32" | "f64" | "f128") => true,
            _ => false,
        }
    }

    #[inline(always)]
    pub fn get_path(&self) -> Option<Path> {
        match self {
            Ty::Never => Some(Path::from("never")),
            Ty::Any => Some(Path::from("any")),
            Ty::Var(v) => Some(v.path().clone()),
            Ty::Projection(s, _) => Some(Path::from(s.clone())),
            Ty::Cast(_, t) | Ty::Qualified(_, t) | Ty::All(_, t) => t.get_path(),
            Ty::Array(..) | Ty::Ptr(_) | Ty::Tuple(_) | Ty::Union(_) | Ty::Func(_, _) => None,
        }
    }

    pub fn name(&self) -> String {
        match self {
            Ty::Never => str!("never"),
            Ty::Any => str!("any"),
            Ty::Tuple(_) => str!("tuple"),
            Ty::Var(v) => v.path().name().unwrap(),
            Ty::Projection(s, _) => s.clone(),
            Ty::Cast(_, t) | Ty::Qualified(_, t) | Ty::All(_, t) => t.name(),
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
            Ty::Projection(n, _) => match n.as_str() {
                "int" | "uint" => Size::ptr(),
                "i8" | "u8" | "bool" => Size::bytes(1),
                "i16" | "u16" => Size::bytes(2),
                "i32" | "u32" | "f32" => Size::bytes(4),
                "i64" | "u64" | "f64" => Size::bytes(8),
                "i128" | "u128" | "f128" => Size::bytes(16),
                // _ if f.len() != 0 => f
                //     .iter()
                //     .fold(Size::zero(), |acc, ty| acc + Ty::size_of(ty)),
                _ => Size::ptr(),
            },
            Ty::Cast(_, ty) | Ty::Qualified(_, ty) | Ty::All(_, ty) => ty.size_of(),
        }
    }

    pub fn skolemize_freevars(self) -> Ty {
        match self {
            Ty::All(xs, t) => {
                let consts = xs
                    .iter()
                    .enumerate()
                    .map(|(i, _)| Ty::Var(TyVar::from(format!("${}", i))))
                    .collect::<Vec<_>>();
                let sub = Subst::from_types(xs.clone(), consts);
                Ty::All(xs, t).apply_subst(&sub)
            }
            t @ _ => t,
        }
    }

    pub fn quantify(self, tyvars: Vec<TyVar>) -> Ty {
        if tyvars.len() != 0 {
            let t = match self {
                Ty::All(_, t) => t,
                _ => Box::new(self),
            };
            Ty::All(tyvars, t)
        } else {
            self
        }
    }

    pub fn quantify_in_place(&mut self) {
        let tyvars = self.collect_tyvars();
        if tyvars.len() != 0 {
            replace(self, |old_ty| {
                Ty::All(
                    tyvars,
                    if let Ty::All(_, old_ty) = old_ty {
                        old_ty
                    } else {
                        Box::new(old_ty)
                    },
                )
            });
        }
    }

    pub fn unquantify(self) -> Ty {
        match self {
            Ty::All(_, t) => *t,
            t => t,
        }
    }

    pub fn formalize(&self) -> Subst {
        log::debug!("formalize: {}", self);
        match &self {
            Ty::All(_, t) | Ty::Qualified(_, t) => t.formalize(),
            Ty::Func(param_tys, ret_ty) => {
                // bind all type variables in the function type
                let mut c = 'a' as u8;
                let mut subst = Subst::new();
                for p in param_tys.iter().chain(std::iter::once(ret_ty.as_ref())) {
                    if let Ty::Var(v) = p {
                        if !subst.contains_key(v) {
                            let path = v.path().with_name(format!("'{}", c as char));
                            let u = Ty::Var(TyVar(path));
                            subst.insert(v.clone(), u);
                            c += 1;
                        }
                    }
                }
                subst
            }
            _ => Subst::new(),
        }
    }

    pub fn qualify_in_place(&mut self, preds: &Vec<TyPredicate>) {
        let tyvars = self.collect_tyvars();
        let ty = std::mem::replace(self, Ty::unit());
        *self = ty.qualify(preds, &tyvars);
    }

    pub fn qualify(self, preds: &Vec<TyPredicate>, tyvars: &Vec<TyVar>) -> Ty {
        let tyvar_set = tyvars.to_set();
        let mut preds = preds
            .iter()
            .filter_map(|p| {
                if !p.collect_tyvars().iter().to_set().is_disjoint(&tyvar_set) {
                    Some(p.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        preds.sort();
        preds.dedup();
        self.qualify_with(preds)
    }

    fn qualify_with(self, preds: Vec<TyPredicate>) -> Ty {
        if preds.len() != 0 {
            // wrap the type in a qualified type if there are type variables
            match self {
                Ty::All(xs, t) => Ty::All(xs, Box::new(t.qualify_with(preds))),
                Ty::Qualified(q, t) => {
                    log::debug!("prev preds: {:?}", q);
                    Ty::Qualified(preds, t)
                }
                _ => Ty::Qualified(preds, Box::new(self)),
            }
        } else {
            self
        }
    }

    pub fn unqualify(self) -> Ty {
        match self {
            Ty::All(xs, t) => Ty::All(xs, Box::new(t.unqualify())),
            Ty::Qualified(_, t) => *t,
            t => t,
        }
    }
    pub fn nilable(t: Ty) -> Ty {
        Ty::Union(vec![t, Ty::nil()])
    }

    pub fn is_closed(&self) -> bool {
        // A type x is closed if fv(x) = ∅
        //   close(x, x', V) => (x' = All[X](x)),
        //   where X = fv(x) - V and V is a set of type variables
        self.free_vars().len() == 0
    }

    pub fn open(self) -> Ty {
        if let Ty::All(_, t) = self {
            *t
        } else {
            self
        }
    }

    pub fn close(self, vs: &HashSet<&TyVar>) -> Ty {
        match self {
            Ty::All(_, t) => t.close(vs),
            _ => {
                let xs = self
                    .free_vars()
                    .difference(vs)
                    .map(|t| *t)
                    .cloned()
                    .collect::<Vec<_>>();
                if xs.len() == 0 {
                    self
                } else {
                    Ty::All(xs, Box::new(self))
                }
            }
        }
    }

    pub fn has_unknowns(&self) -> bool {
        self.collect_tyvars().len() != 0
    }

    pub fn unify_with<A, B, F, G>(
        &self,
        other: &Ty,
        mut f: F,
        g: G,
    ) -> Result<(A, Vec<B>), InferError>
    where
        F: FnMut(Subst) -> A,
        G: Fn(&Ty, &Ty) -> B,
    {
        match (self, other) {
            (_, Ty::Any) | (_, Ty::Never) => Ok((f(Subst::new()), vec![])),
            (Ty::Cast(_, dst), t) | (t, Ty::Cast(_, dst)) => dst.unify_with(t, f, g),
            (Ty::Var(tv), t) | (t, Ty::Var(tv)) if self != other => {
                if !t.free_vars().contains(&tv) {
                    Ok((f(subst! { tv.clone() => t.clone() }), vec![]))
                } else {
                    return Err(InferError {
                        msg: format!("recursive unification: {} and {}", self, other),
                        src: vec![],
                    });
                }
            }
            (Ty::Tuple(a), Ty::Tuple(b)) => {
                let mut z = vec![];
                for (x, y) in a.iter().zip(b.iter()) {
                    z.push(g(x, y));
                }
                Ok((f(Subst::new()), z))
            }
            (Ty::Ptr(a), Ty::Ptr(b)) => a.unify_with(b, f, g),
            (Ty::Projection(a, s), Ty::Projection(b, t)) if a == b => {
                let mut b = vec![];
                for (x, y) in s.iter().zip(t.iter()) {
                    b.push(g(x, y));
                }
                Ok((f(Subst::new()), b))
            }
            (Ty::Func(r, s), Ty::Func(t, u)) if r.len() == t.len() => {
                let mut b = vec![];
                for (x, y) in r.iter().zip(t.iter()) {
                    b.push(g(x, y));
                }
                b.push(g(s, u));
                Ok((f(Subst::new()), b))
            }
            (Ty::Union(s), Ty::Union(t)) if s.len() == t.len() => {
                let mut b = vec![];
                for (x, y) in s.iter().zip(t.iter()) {
                    b.push(g(x, y));
                }
                Ok((f(Subst::new()), b))
            }
            // (Ty::Union(tys), t) if !matches!(t, Ty::Union(_)) => {
            //     let mut b = vec![];
            //     for s in tys {
            //         b.push(g(s, t));
            //     }
            //     Ok((f(Subst::new()), b))
            // }
            // (s, Ty::Union(tys)) if !matches!(s, Ty::Union(_)) => {
            //     let mut b = vec![];
            //     for t in tys {
            //         b.push(g(t, s));
            //     }
            //     Ok((f(Subst::new()), b))
            // }
            (Ty::Qualified(p, s), Ty::Qualified(q, t)) if p == q => {
                Ok((f(Subst::new()), vec![g(s, t)]))
            }
            (Ty::Qualified(_, s), t) => s.unify_with(t, f, g),
            (s, Ty::Qualified(_, t)) => s.unify_with(t, f, g),
            (Ty::All(xs, s), Ty::All(ys, t)) if xs.len() == ys.len() => {
                Ok((f(Subst::new()), vec![g(s, t)]))
            }
            (Ty::All(_, s), t) => s.unify_with(t, f, g),
            (s, Ty::All(_, t)) => s.unify_with(t, f, g),
            _ => {
                return Err(InferError {
                    msg: format!("type mismatch `{}` and `{}`", self, other),
                    src: vec![],
                })
            }
        }
    }

    pub fn mgu(&self, other: &Ty) -> Result<Subst, InferError> {
        let (sub, subs) = self.unify_with(other, |sub| sub, |x, y| x.mgu(y))?;
        let mut sub = sub;
        for s in subs {
            sub = sub.union(s?);
        }
        Ok(sub)
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
            (Ty::All(xs, s), Ty::All(ys, t)) if xs == ys => s.is_subtype(t),
            _ if self == t => true,
            _ => false,
        }
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, Ty::Tuple(tys) if tys.is_empty())
    }

    pub fn is_nullary(&self) -> bool {
        match self {
            Ty::Never | Ty::Any | Ty::Union(_) | Ty::Var(_) => true,
            Ty::Projection(_, tys) | Ty::Tuple(tys) => tys.len() == 0,
            Ty::Cast(_, t) | Ty::Qualified(_, t) | Ty::All(_, t) => t.is_nullary(),
            Ty::Func(_, _) | Ty::Array(_, _) | Ty::Ptr(_) => false,
        }
    }

    pub fn is_polymorphic(&self) -> bool {
        self.has_unknowns()
    }

    pub fn is_func(&self) -> bool {
        match &self {
            Ty::All(_, ty) | Ty::Qualified(_, ty) => ty.is_func(),
            Ty::Func(..) => true,
            _ => false,
        }
    }

    pub fn is_funcs_union(&self) -> bool {
        match &self {
            Ty::All(_, ty) => ty.is_funcs_union(),
            Ty::Union(tys) => tys.iter().all(|t| t.is_func()),
            _ => false,
        }
    }

    pub fn is_union(&self) -> bool {
        match &self {
            Ty::All(_, ty) => ty.is_union(),
            Ty::Union(_) => true,
            _ => false,
        }
    }

    pub fn is_tyvar(&self) -> bool {
        matches!(self, Ty::Var(_))
    }

    pub fn as_tyvar(self) -> TyVar {
        match self {
            Ty::Var(v) => v,
            _ => panic!("not a type variable"),
        }
    }

    pub fn get_ty_params(&self) -> Vec<&Ty> {
        match self {
            Ty::All(_, t) => t.get_ty_params(),
            Ty::Qualified(_, t) => t.get_ty_params(),
            Ty::Cast(_, dst) => dst.get_ty_params(),
            Ty::Array(t, _) | Ty::Ptr(t) => vec![t.as_ref()],
            Ty::Tuple(t) | Ty::Union(t) | Ty::Projection(_, t) => t.iter().collect(),
            Ty::Never | Ty::Any | Ty::Var(_) | Ty::Func(_, _) => vec![],
        }
    }

    pub fn get_ty_param_at(&self, idx: usize) -> &Ty {
        match self {
            Ty::All(_, t) => t.get_ty_param_at(idx),
            Ty::Qualified(_, t) => t.get_ty_param_at(idx),
            Ty::Cast(_, dst) => dst.get_ty_param_at(idx),
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
            Ty::Never | Ty::Any | Ty::Var(_) | Ty::Func(_, _) => {
                panic!("no type parameters: {}", self)
            }
        }
    }

    pub fn union(&mut self, ty: Ty) {
        log::debug!("union: {} | {}", self, ty);
        match (self, ty) {
            (Ty::All(xs, t), Ty::All(ys, u)) => {
                for y in ys {
                    if !xs.contains(&y) {
                        xs.push(y);
                    }
                }
                t.union(*u);
            }
            (Ty::All(_, t), u) => t.union(u),
            (t, Ty::All(xs, u)) => replace(t, |mut t| {
                t.union(*u);
                Ty::All(xs, Box::new(t))
            }),
            (Ty::Qualified(p, t), Ty::Qualified(q, u)) => {
                p.extend(q);
                t.union(*u);
            }
            (Ty::Qualified(_, t), u) => {
                t.union(u);
            }
            (t, Ty::Qualified(p, u)) => replace(t, |mut t| {
                t.union(*u);
                Ty::Qualified(p, Box::new(t))
            }),
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

    pub fn add_to_union(&mut self, ty: Ty) {
        if let Ty::All(_, t) = self {
            t.as_mut().add_to_union(ty);
        } else if let Ty::Union(tys) = self {
            tys.push(ty);
        }
    }

    pub fn unpack_quantified_ty(self) -> (Vec<TyVar>, Ty) {
        match self {
            Ty::All(q, t) => (q, *t),
            t => (vec![], t),
        }
    }

    pub fn unpack_qualified_ty(self) -> (Vec<TyPredicate>, Ty) {
        match self {
            Ty::All(xs, t) => {
                let (q, t) = t.unpack_qualified_ty();
                (q, Ty::All(xs, Box::new(t)))
            }
            Ty::Qualified(q, t) => (q, *t),
            t => (vec![], t),
        }
    }

    pub fn unpack_tuple(self) -> Vec<Ty> {
        match self {
            Ty::Tuple(tys) => tys,
            _ => panic!("not a tuple type"),
        }
    }

    pub fn try_unpack_overloaded_fn<T: Copy + Clone>(self) -> Result<Vec<Ty>, InferError> {
        if !self.is_func() && !self.is_funcs_union() {
            return Err(InferError {
                msg: format!("expected function type but found {}", self),
                src: vec![],
            });
        }

        match self {
            Ty::Func(p, r) => Ok(vec![Ty::Func(p, r)]),
            Ty::All(xs, t) if t.is_func() => Ok(vec![Ty::All(xs, t)]),
            Ty::Union(tys) => Ok(tys),
            t => unreachable!("attempted to unpack non-function: {:?}", t),
        }
    }

    pub fn try_borrow_fn(
        &self,
    ) -> Result<
        (
            Option<&Vec<TyVar>>,
            Option<&Vec<TyPredicate>>,
            &Vec<Ty>,
            &Ty,
        ),
        InferError,
    > {
        if !self.is_func() {
            return Err(InferError {
                msg: format!("expected function type but found {}", self),
                src: vec![],
            });
        }

        match self {
            Ty::All(xs, ty) => {
                let (_, q, p, r) = ty.try_borrow_fn()?;
                Ok((Some(xs), q, p, r))
            }
            Ty::Qualified(q, ty) => {
                let (_, _, p, r) = ty.try_borrow_fn()?;
                Ok((None, Some(q), p, r))
            }
            Ty::Func(p, r) => Ok((None, None, p, r.as_ref())),
            _ => unreachable!("attempted to unpack non-function: {:?}", self),
        }
    }

    pub fn try_unpack_fn(
        self,
    ) -> Result<(Option<Vec<TyVar>>, Vec<TyPredicate>, Vec<Ty>, Ty), InferError> {
        if !self.is_func() {
            return Err(InferError {
                msg: format!("expected function type but found {}", self),
                src: vec![],
            });
        }

        match self {
            Ty::All(xs, ty) => {
                let (_, q, p, r) = ty.try_unpack_fn()?;
                Ok((Some(xs), q, p, r))
            }
            Ty::Qualified(q, ty) => {
                let (_, _, p, r) = ty.try_unpack_fn()?;
                Ok((None, q, p, r))
            }
            Ty::Func(p, r) => Ok((None, vec![], p, *r)),
            _ => unreachable!("attempted to unpack non-function: {:?}", self),
        }
    }
}

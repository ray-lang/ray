use std::{
    collections::{HashMap, HashSet},
    ops::BitOr,
};

use crate::{
    ast::{self, FnSig, HasSource, Path},
    errors::{RayError, RayErrorKind},
    pathlib::FilePath,
    span::Source,
    utils::join,
};

use super::{
    context::Ctx,
    predicate::TyPredicate,
    state::TyVarFactory,
    subst::{ApplySubst, Subst},
    traits::{Generalize, HasFreeVars, Instantiate, Polymorphize, Skolemize},
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
        if f.alternate() {
            write!(f, "{}", self.0)
        } else {
            if let Some(name) = self.0.name() {
                write!(f, "{}", name)
            } else {
                write!(f, "")
            }
        }
    }
}

impl ApplySubst for TyVar {
    fn apply_subst(self, subst: &Subst) -> TyVar {
        if let Some(Ty::Var(v)) = subst.get(&self) {
            v.clone()
        } else {
            self
        }
    }
}

impl Polymorphize for TyVar {
    fn polymorphize(self, tf: &mut TyVarFactory, subst: &mut HashMap<Ty, TyVar>) -> Self {
        if let Some(tv) = subst.get(&Ty::Var(self.clone())) {
            tv.clone()
        } else {
            let tv = tf.next();
            subst.insert(Ty::Var(self), tv.clone());
            tv
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StructTy {
    pub path: ast::Path,
    pub ty: Ty,
    pub fields: Vec<(String, Ty)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraitTy {
    pub path: ast::Path,
    pub ty: Ty,
    pub super_traits: Vec<Ty>,
    pub fields: Vec<(String, Ty)>,
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
    Union(Vec<Ty>),
    Func(Vec<Ty>, Box<Ty>),
    Projection(String, Vec<Ty>, Vec<Ty>),
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
            Ty::Union(tys) => {
                if tys.len() != 0 {
                    write!(f, "{}", join(tys, " | "))
                } else {
                    write!(f, "()")
                }
            }
            Ty::Func(a, r) => write!(f, "({}) -> {}", join(a, ", "), r),
            Ty::Projection(n, t, _) => {
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
            Ty::Any | Ty::Never => self.clone(),
            Ty::Var(v) => subst.get_var(&v),
            Ty::Union(tys) => {
                let mut tys = tys.apply_subst(subst);
                tys.sort();
                tys.dedup(); // remove any duplicates
                if tys.len() == 1 {
                    tys.pop().unwrap()
                } else {
                    Ty::Union(tys.apply_subst(subst))
                }
            }
            Ty::Func(a, r) => Ty::Func(a.apply_subst(subst), r.apply_subst(subst)),
            Ty::Projection(n, t, f) => {
                Ty::Projection(n, t.apply_subst(subst), f.apply_subst(subst))
            }
            Ty::Cast(f, t) => Ty::Cast(f.apply_subst(subst), t.apply_subst(subst)),
            Ty::Qualified(p, t) => Ty::Qualified(p.apply_subst(subst), t.apply_subst(subst)),
            Ty::All(xs, ty) => Ty::All(xs.apply_subst(subst), ty.apply_subst(subst)),
        }
    }
}

impl Generalize for Ty {
    fn generalize(self, m: &Vec<Ty>, preds: &Vec<TyPredicate>) -> Ty {
        // generalize(M, τ) => ∀{a}.τ where {a} = ftv(τ) − ftv(M).
        let tyvars = self
            .free_vars()
            .difference(&m.free_vars())
            .map(|&t| t.clone())
            .collect::<Vec<_>>();

        self.qualify_with_tyvars(preds, &tyvars).quantify(tyvars)
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
            Ty::All(xs, ty) => {
                let xs = xs.iter().collect();
                ty.free_vars().difference(&xs).map(|t| *t).collect()
            }
            Ty::Union(tys) => tys.free_vars(),
            Ty::Projection(_, tys, f) => tys
                .iter()
                .chain(f.iter())
                .flat_map(|t| t.free_vars())
                .collect(),
            Ty::Func(tys, r) => tys
                .iter()
                .chain(std::iter::once(r.as_ref()))
                .flat_map(|t| t.free_vars())
                .collect(),
            Ty::Var(tv) => vec![tv].into_iter().collect(),
            _ => HashSet::new(),
        }
    }
}

impl HasFreeVars for Vec<Ty> {
    fn free_vars(&self) -> HashSet<&TyVar> {
        self.iter().flat_map(|t| t.free_vars()).collect()
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
            Ty::Union(tys) => Ty::Union(tys.polymorphize(tf, subst)),
            Ty::Func(p, r) => Ty::Func(p.polymorphize(tf, subst), r.polymorphize(tf, subst)),
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
            Ty::Func(p, r) => Ty::Func(p.instantiate(tf), r.instantiate(tf)),
            Ty::Cast(src, dst) => Ty::Cast(src.instantiate(tf), dst.instantiate(tf)),
            Ty::Projection(s, tys, f) => Ty::Projection(s, tys.instantiate(tf), f.instantiate(tf)),
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
    pub fn from_sig<Info>(
        sig: &FnSig<Info>,
        fn_scope: &Path,
        filepath: &FilePath,
        fn_ctx: &mut Ctx,
        parent_ctx: &mut Ctx,
    ) -> Result<Ty, RayError>
    where
        Info: std::fmt::Debug + Clone + PartialEq + Eq + HasSource,
    {
        let mut param_tys = vec![];

        for param in sig.params.iter() {
            if let Some(ty) = param.ty() {
                param_tys.push(Ty::from_ast_ty(&ty.kind, &fn_scope, fn_ctx));
            } else {
                return Err(RayError {
                    msg: format!("parameter `{}` must have a type annotation", param),
                    src: vec![Source {
                        span: Some(param.span()),
                        filepath: filepath.clone(),
                    }],
                    kind: RayErrorKind::Type,
                });
            }
        }

        let ret_ty = sig
            .ret_ty
            .as_ref()
            .map(|t| Ty::from_ast_ty(&t.kind, &fn_scope, fn_ctx))
            .unwrap_or_else(|| Ty::unit());

        let mut ty = Ty::Func(param_tys, Box::new(ret_ty));

        if sig.qualifiers.len() != 0 {
            let mut p = vec![];
            for q in sig.qualifiers.iter() {
                p.push(TyPredicate::from_ast_ty(&q, &fn_scope, &filepath, fn_ctx)?);
            }
            ty = Ty::Qualified(p, Box::new(ty));
        }

        let free_vars = parent_ctx.free_vars();
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

    pub fn from_ast_ty(kind: &ast::TypeKind, scope: &ast::Path, ctx: &mut Ctx) -> Ty {
        match kind {
            ast::TypeKind::Unknown => unimplemented!(),
            ast::TypeKind::Basic {
                name, ty_params, ..
            } => {
                if let Some(ty) = ctx.get_var(name) {
                    ty.clone()
                } else {
                    let scope = scope.append(name);
                    let ty_params = if let Some(ty_params) = ty_params {
                        ty_params
                            .tys
                            .iter()
                            .map(|t| Ty::from_ast_ty(&t.kind, &scope, ctx))
                            .collect()
                    } else {
                        vec![]
                    };
                    Ty::Projection(name.to_string(), ty_params, vec![])
                }
            }
            ast::TypeKind::Generic(name) => {
                let fqn = scope.append(format!("'{}", name));
                let fqn_string = fqn.to_string();
                if let Some(ty) = ctx.get_var(&fqn_string) {
                    ty.clone()
                } else {
                    let tv = TyVar(fqn);
                    let ty = Ty::Var(tv);
                    ctx.bind_var(fqn_string, ty.clone());
                    ty
                }
            }
            ast::TypeKind::Struct {
                name,
                ty_params,
                fields,
            } => {
                if let Some(ty) = ctx.get_var(name) {
                    ty.clone()
                } else {
                    let scope = scope.append(name);
                    let ty_params = if let Some(ty_params) = ty_params {
                        ty_params
                            .tys
                            .iter()
                            .map(|t| Ty::from_ast_ty(&t.kind, &scope, ctx))
                            .collect()
                    } else {
                        vec![]
                    };

                    let fields = if let Some(fields) = fields {
                        fields
                            .iter()
                            .map(|(_, t)| Ty::from_ast_ty(&t.kind, &scope, ctx))
                            .collect()
                    } else {
                        vec![]
                    };

                    Ty::Projection(name.to_string(), ty_params, fields)
                }
            }
            ast::TypeKind::Fn {
                ty_params,
                params,
                ret,
            } => unimplemented!(),
            ast::TypeKind::Pointer(t) => Ty::Projection(
                str!("Ptr"),
                vec![Ty::from_ast_ty(&t.kind, scope, ctx)],
                vec![],
            ),
            ast::TypeKind::Bool => Ty::bool(),
            ast::TypeKind::Char => Ty::char(),
            ast::TypeKind::String => Ty::string(),
            ast::TypeKind::Nil => Ty::nil(),
            ast::TypeKind::Int(i) => match i {
                ast::IntTy::Int => Ty::int(),
                ast::IntTy::Int8 => Ty::i8(),
                ast::IntTy::Int16 => Ty::i16(),
                ast::IntTy::Int32 => Ty::i32(),
                ast::IntTy::Int64 => Ty::i64(),
                ast::IntTy::Int128 => Ty::i128(),
                ast::IntTy::UInt => Ty::uint(),
                ast::IntTy::UInt8 => Ty::u8(),
                ast::IntTy::UInt16 => Ty::u16(),
                ast::IntTy::UInt32 => Ty::u32(),
                ast::IntTy::UInt64 => Ty::u64(),
                ast::IntTy::UInt128 => Ty::u128(),
            },
            ast::TypeKind::Float(f) => match f {
                ast::FloatTy::Float32 => Ty::f32(),
                ast::FloatTy::Float64 => Ty::f64(),
                ast::FloatTy::Float128 => Ty::f128(),
            },
            ast::TypeKind::List(t) => {
                let el_ty = Ty::from_ast_ty(&t.kind, scope, ctx);
                let fields = vec![Ty::ptr(el_ty.clone()), Ty::uint()];
                Ty::Projection(str!("List"), vec![el_ty.clone()], fields)
            }
            ast::TypeKind::Sequence(tys) => {
                let fields = tys
                    .iter()
                    .map(|t| Ty::from_ast_ty(&t.kind, scope, ctx))
                    .collect::<Vec<_>>();
                Ty::Projection(str!("tuple"), fields.clone(), fields)
            }
            ast::TypeKind::Array(t, s) => Ty::Projection(
                format!("array[{}]", s),
                vec![Ty::from_ast_ty(&t.kind, scope, ctx)],
                vec![],
            ),
            ast::TypeKind::TypeVar(_) => unimplemented!(),
            ast::TypeKind::Union(tys) => {
                if tys.len() != 0 {
                    unimplemented!()
                } else {
                    Ty::unit()
                }
            }
        }
    }

    #[inline(always)]
    pub fn unit() -> Ty {
        Ty::Union(vec![])
    }

    #[inline(always)]
    pub fn con<S: Into<String>>(s: S) -> Ty {
        Ty::Projection(s.into(), vec![], vec![])
    }

    #[inline(always)]
    pub fn ptr(ty: Ty) -> Ty {
        Ty::Projection(str!("Ptr"), vec![ty], vec![])
    }

    #[inline(always)]
    pub fn ty_type(ty: Ty) -> Ty {
        Ty::Projection(str!("type"), vec![ty], vec![])
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
        Ty::con("string")
    }

    #[inline(always)]
    pub fn bytes() -> Ty {
        Ty::con("bytes")
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
            Ty::Projection(a, _, _)
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
            Ty::Projection(a, _, _) if matches!(a.as_str(), "float" | "f32" | "f64" | "f128") => {
                true
            }
            _ => false,
        }
    }

    #[inline(always)]
    pub fn get_path(&self) -> Option<Path> {
        match self {
            Ty::Never => Some(Path::from("never")),
            Ty::Any => Some(Path::from("any")),
            Ty::Projection(s, _, _) => Some(Path::from(s.clone())),
            Ty::Cast(_, t) | Ty::Qualified(_, t) | Ty::All(_, t) => t.get_path(),
            Ty::Var(_) | Ty::Union(_) | Ty::Func(_, _) => None,
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
            Ty::All(tyvars, Box::new(self))
        } else {
            self
        }
    }

    pub fn unquantify(self) -> Ty {
        match self {
            Ty::All(_, t) => *t,
            t => t,
        }
    }

    pub fn formalize(&self) -> Subst {
        match &self {
            Ty::All(_, t) | Ty::Qualified(_, t) => t.formalize(),
            Ty::Func(param_tys, ret_ty) => {
                // bind all type variables in the function type
                let mut c = 'a' as u8;
                let mut subst = Subst::new();
                for p in param_tys.iter().chain(std::iter::once(ret_ty.as_ref())) {
                    if let Ty::Var(v) = p {
                        if !subst.contains_key(v) {
                            let u = Ty::Var(TyVar(format!("'{}", c as char).into()));
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

    pub fn qualify_with_tyvars(self, preds: &Vec<TyPredicate>, tyvars: &Vec<TyVar>) -> Ty {
        let tyvar_set = tyvars.iter().collect::<HashSet<_>>();
        let q = preds
            .iter()
            .filter_map(|p| {
                if !p.free_vars().is_disjoint(&tyvar_set) {
                    Some(p.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if q.len() != 0 {
            // wrap the type in a qualified type if there are type variables
            match self {
                Ty::All(xs, t) => Ty::All(xs, Box::new(Ty::Qualified(q, t))),
                _ => Ty::Qualified(q, Box::new(self)),
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
            // prioritize bound variables over free variables
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
            (Ty::Projection(a, s, _), Ty::Projection(b, t, _)) if a == b => {
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
            (Ty::Projection(a, s, _), Ty::Projection(b, t, _)) => {
                a == b && s.iter().zip(t.iter()).all(|(x, y)| x.is_subtype(y))
            }
            (Ty::Func(r, s), Ty::Func(t, u)) => {
                r.iter().zip(t.iter()).all(|(x, y)| x.is_subtype(y)) && s.is_subtype(u)
            }
            (Ty::All(xs, s), Ty::All(ys, t)) if xs == ys => s.is_subtype(t),
            _ if self == t => true,
            _ => false,
        }
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, Ty::Union(tys) if tys.is_empty())
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

    pub fn collect_tyvars(&self) -> Vec<TyVar> {
        let mut vs = match self {
            Ty::All(_, t) => t.collect_tyvars(),
            Ty::Qualified(_, t) => t.collect_tyvars(),
            Ty::Func(param_tys, ret) => param_tys
                .iter()
                .chain(std::iter::once(ret.as_ref()))
                .flat_map(|t| t.collect_tyvars())
                .collect(),
            Ty::Var(v) => vec![v.clone()].into_iter().collect(),
            Ty::Union(t) | Ty::Projection(_, t, _) => {
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
            Ty::Union(t) | Ty::Projection(_, t, _) => t.iter().collect(),
            Ty::Never | Ty::Any | Ty::Var(_) | Ty::Func(_, _) => vec![],
        }
    }

    pub fn get_ty_param_at(&self, idx: usize) -> &Ty {
        match self {
            Ty::All(_, t) => t.get_ty_param_at(idx),
            Ty::Qualified(_, t) => t.get_ty_param_at(idx),
            Ty::Cast(_, dst) => dst.get_ty_param_at(idx),
            Ty::Union(t) | Ty::Projection(_, t, _) => t.iter().nth(idx).unwrap(),
            Ty::Never | Ty::Any | Ty::Var(_) | Ty::Func(_, _) => {
                panic!("no type parameters: {}", self)
            }
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

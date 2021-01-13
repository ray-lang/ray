use std::{
    collections::{HashMap, HashSet},
    ops::BitOr,
};

use crate::{
    ast::{self, FnSig, Path},
    errors::{RayError, RayErrorKind},
    pathlib::FilePath,
    span::Source,
    utils::join,
};

use super::{
    context::Ctx,
    predicate::{PredicateEntails, TyPredicate},
    subst::{ApplySubst, Subst},
    top::{
        state::TyVarFactory,
        traits::{FreezeVars, Generalize, HasFreeVars, Skolemize},
    },
    InferError,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TyVar(pub String);

impl std::fmt::Display for TyVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
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
    Bound(TyVar),
    Var(TyVar),
    Union(Vec<Ty>),
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
            Ty::Bound(v) | Ty::Var(v) => write!(f, "{}", v),
            Ty::Union(tys) => {
                if tys.len() != 0 {
                    write!(f, "{}", join(tys, " | "))
                } else {
                    write!(f, "()")
                }
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
            Ty::Any | Ty::Never => self.clone(),
            Ty::Bound(v) | Ty::Var(v) => subst.get_var(&v),
            Ty::Union(tys) => {
                let mut tys = tys.apply_subst(subst);
                tys.dedup(); // remove any duplicates
                if tys.len() == 1 {
                    tys.pop().unwrap()
                } else {
                    Ty::Union(tys.apply_subst(subst))
                }
            }
            Ty::Func(a, r) => Ty::Func(a.apply_subst(subst), Box::new(r.apply_subst(subst))),
            Ty::Projection(n, t) => Ty::Projection(n, t.apply_subst(subst)),
            Ty::Cast(f, t) => Ty::Cast(
                Box::new(f.apply_subst(subst)),
                Box::new(t.apply_subst(subst)),
            ),
            Ty::Qualified(p, t) => {
                Ty::Qualified(p.apply_subst(subst), Box::new(t.apply_subst(subst)))
            }
            Ty::All(xs, ty) => Ty::All(xs.apply_subst(subst), Box::new(ty.apply_subst(subst))),
        }
    }
}

impl ApplySubst<Vec<(String, Ty)>> for Vec<(String, Ty)> {
    fn apply_subst(self, subst: &Subst) -> Vec<(String, Ty)> {
        self.into_iter()
            .map(|(n, t)| (n, t.apply_subst(subst)))
            .collect()
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
            Ty::Union(tys) | Ty::Projection(_, tys) => tys.free_vars(),
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

impl Skolemize for Ty {
    fn skolemize(&self, sf: &mut TyVarFactory) -> (Self, Vec<TyVar>)
    where
        Self: Sized,
    {
        println!("pre-skolemized: {}", self);
        let ty = self.clone();
        let prev_vars = ty.collect_tyvars();
        let ty = ty.instantiate(sf).generalize(&vec![], &vec![]);
        println!("skolemized: {}", ty);
        let mut vars = ty.collect_tyvars();
        for v in prev_vars {
            if let Some(pos) = vars.iter().position(|x| x == &v) {
                vars.remove(pos);
            }
        }
        (ty, vars)
    }
}

impl FreezeVars for Ty {
    fn freeze_tyvars(self) -> Ty {
        match self {
            Ty::Var(v) => Ty::Bound(v),
            Ty::Union(tys) => Ty::Union(tys.freeze_tyvars()),
            Ty::Func(p, r) => Ty::Func(p.freeze_tyvars(), Box::new(r.freeze_tyvars())),
            Ty::Projection(s, tys) => Ty::Projection(s, tys.freeze_tyvars()),
            Ty::Cast(src, dst) => {
                Ty::Cast(Box::new(src.freeze_tyvars()), Box::new(dst.freeze_tyvars()))
            }
            Ty::Qualified(p, t) => Ty::Qualified(p.freeze_tyvars(), Box::new(t.freeze_tyvars())),
            Ty::All(xs, t) => Ty::All(xs, Box::new(t.freeze_tyvars())),
            t @ _ => t,
        }
    }

    fn unfreeze_tyvars(self) -> Self {
        match self {
            Ty::Bound(v) => Ty::Var(v),
            Ty::Union(tys) => Ty::Union(tys.unfreeze_tyvars()),
            Ty::Func(p, r) => Ty::Func(p.unfreeze_tyvars(), Box::new(r.unfreeze_tyvars())),
            Ty::Projection(s, tys) => Ty::Projection(s, tys.unfreeze_tyvars()),
            Ty::Cast(src, dst) => Ty::Cast(
                Box::new(src.unfreeze_tyvars()),
                Box::new(dst.unfreeze_tyvars()),
            ),
            Ty::Qualified(p, t) => {
                Ty::Qualified(p.unfreeze_tyvars(), Box::new(t.unfreeze_tyvars()))
            }
            Ty::All(xs, t) => Ty::All(xs, Box::new(t.unfreeze_tyvars())),
            t @ _ => t,
        }
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
    pub fn from_sig(
        sig: &FnSig,
        fn_scope: &Path,
        filepath: &FilePath,
        fn_ctx: &mut Ctx,
        parent_ctx: &mut Ctx,
    ) -> Result<Ty, RayError> {
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
                    Ty::Projection(name.to_string(), ty_params)
                }
            }
            ast::TypeKind::Generic(name) => {
                let fqn = scope.append(name).to_string();
                if let Some(ty) = ctx.get_var(&fqn) {
                    ty.clone()
                } else {
                    let tv = TyVar(fqn.clone());
                    let ty = Ty::Var(tv);
                    ctx.bind_var(fqn, ty.clone());
                    ty
                }
            }
            ast::TypeKind::Struct {
                name,
                ty_params,
                fields,
            } => unimplemented!(),
            ast::TypeKind::Fn {
                ty_params,
                params,
                ret,
            } => unimplemented!(),
            ast::TypeKind::Pointer(t) => {
                Ty::Projection(str!("Ptr"), vec![Ty::from_ast_ty(&t.kind, scope, ctx)])
            }
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
                ast::FloatTy::Float32 => Ty::Projection(str!("f32"), vec![]),
                ast::FloatTy::Float64 => Ty::Projection(str!("f64"), vec![]),
                ast::FloatTy::Float128 => Ty::Projection(str!("f28"), vec![]),
            },
            ast::TypeKind::List(t) => {
                Ty::Projection(str!("List"), vec![Ty::from_ast_ty(&t.kind, scope, ctx)])
            }
            ast::TypeKind::Sequence(tys) => Ty::Projection(
                str!("tuple"),
                tys.iter()
                    .map(|t| Ty::from_ast_ty(&t.kind, scope, ctx))
                    .collect(),
            ),
            ast::TypeKind::Array(t, s) => Ty::Projection(
                format!("array[{}]", s),
                vec![Ty::from_ast_ty(&t.kind, scope, ctx)],
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

    pub fn unit() -> Ty {
        Ty::Union(vec![])
    }

    pub fn ty_type(ty: Ty) -> Ty {
        Ty::Projection(str!("type"), vec![ty])
    }

    pub fn nil() -> Ty {
        Ty::Projection(str!("nil"), vec![])
    }

    pub fn bool() -> Ty {
        Ty::Projection(str!("bool"), vec![])
    }

    pub fn char() -> Ty {
        Ty::Projection(str!("char"), vec![])
    }

    pub fn string() -> Ty {
        Ty::Projection(str!("string"), vec![])
    }

    pub fn bytes() -> Ty {
        Ty::Projection(str!("bytes"), vec![])
    }

    pub fn int() -> Ty {
        Ty::Projection(str!("int"), vec![])
    }

    pub fn i8() -> Ty {
        Ty::Projection(str!("i8"), vec![])
    }

    pub fn i16() -> Ty {
        Ty::Projection(str!("i16"), vec![])
    }

    pub fn i32() -> Ty {
        Ty::Projection(str!("i32"), vec![])
    }

    pub fn i64() -> Ty {
        Ty::Projection(str!("i64"), vec![])
    }

    pub fn i128() -> Ty {
        Ty::Projection(str!("i128"), vec![])
    }

    pub fn uint() -> Ty {
        Ty::Projection(str!("uint"), vec![])
    }

    pub fn u8() -> Ty {
        Ty::Projection(str!("u8"), vec![])
    }

    pub fn u16() -> Ty {
        Ty::Projection(str!("u16"), vec![])
    }

    pub fn u32() -> Ty {
        Ty::Projection(str!("u32"), vec![])
    }

    pub fn u64() -> Ty {
        Ty::Projection(str!("u64"), vec![])
    }

    pub fn u128() -> Ty {
        Ty::Projection(str!("u128"), vec![])
    }

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

    pub fn float() -> Ty {
        Ty::Projection(str!("float"), vec![])
    }

    pub fn f32() -> Ty {
        Ty::Projection(str!("f32"), vec![])
    }

    pub fn f64() -> Ty {
        Ty::Projection(str!("f64"), vec![])
    }

    pub fn f128() -> Ty {
        Ty::Projection(str!("f128"), vec![])
    }

    pub fn is_float_ty(&self) -> bool {
        match self {
            Ty::Projection(a, _) if matches!(a.as_str(), "float" | "f32" | "f64" | "f128") => true,
            _ => false,
        }
    }

    pub fn get_path(&self) -> Option<Path> {
        match self {
            Ty::Never => Some(Path::from("never")),
            Ty::Any => Some(Path::from("any")),
            Ty::Projection(s, _) => Some(Path::from(s)),
            Ty::Cast(_, t) | Ty::Qualified(_, t) | Ty::All(_, t) => t.get_path(),
            Ty::Bound(_) | Ty::Var(_) | Ty::Union(_) | Ty::Func(_, _) => None,
        }
    }

    pub fn instantiate(self, tf: &mut TyVarFactory) -> Ty {
        match self {
            Ty::Var(v) => Ty::Var(v),
            Ty::Bound(v) => Ty::Bound(v),
            Ty::Union(tys) => Ty::Union(tys.into_iter().map(|t| t.instantiate(tf)).collect()),
            Ty::Func(p, r) => Ty::Func(
                p.into_iter().map(|t| t.instantiate(tf)).collect(),
                Box::new(r.instantiate(tf)),
            ),
            Ty::Cast(src, dst) => {
                Ty::Cast(Box::new(src.instantiate(tf)), Box::new(dst.instantiate(tf)))
            }
            Ty::Projection(s, tys) => {
                Ty::Projection(s, tys.into_iter().map(|t| t.instantiate(tf)).collect())
            }
            Ty::Qualified(p, t) => Ty::Qualified(
                p.into_iter().map(|t| t.instantiate(tf)).collect(),
                Box::new(t.instantiate(tf)),
            ),
            Ty::All(xs, t) => {
                let new_xs = (0..xs.len()).into_iter().map(|_| Ty::Var(tf.next()));
                let sub = Subst::from_types(xs, new_xs);
                t.apply_subst(&sub)
            }
            t @ Ty::Never | t @ Ty::Any => t,
        }
    }

    pub fn skolemize_freevars(self) -> Ty {
        match self {
            Ty::All(xs, t) => {
                let consts = xs
                    .iter()
                    .enumerate()
                    .map(|(i, _)| Ty::Var(TyVar(format!("${}", i))))
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

    // pub fn instantiate(
    //     self,
    //     reverse_subst: &mut HashMap<TyVar, TyVar>,
    //     tf: &mut TyVarFactory,
    // ) -> Ty {
    //     match self {
    //         Ty::Var(v) => {
    //             if let Some(v) = reverse_subst.get(&v) {
    //                 Ty::Var(v.clone())
    //             } else {
    //                 let u = tf.next();
    //                 reverse_subst.insert(v, u.clone());
    //                 Ty::Var(u)
    //             }
    //         }
    //         Ty::Union(tys) => Ty::Union(
    //             tys.into_iter()
    //                 .map(|t| t.instantiate(reverse_subst, tf))
    //                 .collect(),
    //         ),
    //         Ty::Func(p, r) => Ty::Func(
    //             p.into_iter()
    //                 .map(|t| t.instantiate(reverse_subst, tf))
    //                 .collect(),
    //             Box::new(r.instantiate(reverse_subst, tf)),
    //         ),
    //         Ty::Cast(src, dst) => Ty::Cast(
    //             Box::new(src.instantiate(reverse_subst, tf)),
    //             Box::new(dst.instantiate(reverse_subst, tf)),
    //         ),
    //         Ty::Projection(s, tys) => Ty::Projection(
    //             s,
    //             tys.into_iter()
    //                 .map(|t| t.instantiate(reverse_subst, tf))
    //                 .collect(),
    //         ),
    //         Ty::Qualified(p, t) => Ty::Qualified(
    //             p.into_iter()
    //                 .map(|t| t.instantiate(reverse_subst, tf))
    //                 .collect(),
    //             Box::new(t.instantiate(reverse_subst, tf)),
    //         ),
    //         Ty::All(_, t) => t.instantiate(reverse_subst, tf),
    //         t @ Ty::Never | t @ Ty::Any => t,
    //     }
    // }

    // pub fn instance_of(&self, u: &Ty, ctx: &Ctx) -> bool {
    //     println!("instance_of: {} < {}", self, u);
    //     let t = self.clone().skolemize_freevars();
    //     println!("skolemized free_vars: t = {}", t);
    //     let (xs, t) = t.unpack_quantified_ty();
    //     let u = u.clone().skolemize_freevars();
    //     println!("skolemized free_vars: u = {}", u);
    //     let args = (0..xs.len())
    //         .into_iter()
    //         .map(|i| Ty::Var(TyVar(format!("#{}", i))));
    //     let sub = Subst::from_types(xs, args);
    //     let (p, t) = t.apply_subst(&sub).unpack_qualified_ty();
    //     println!("tmp vars: p = {:?}", p);
    //     println!("tmp vars: t = {}", t);
    //     let mut tf = TyVarFactory::new("@");
    //     let (q, u) = u.instantiate(&mut tf).unpack_qualified_ty();
    //     println!("instantiated: p = {:?}", p);
    //     println!("instantiated: u = {}", u);
    //     let sub = match t.mgu(&u) {
    //         Ok(s) => s,
    //         _ => return false,
    //     };

    //     println!("unify: sub = {}", sub);
    //     q.apply_subst(&sub).iter().all(|q| p.entails(q, ctx))
    // }

    // pub fn instance_of(&self, r: &Ty) -> bool {
    //     println!("instance_of: {} < {}", self, r);
    //     match (self, r) {
    //         (Ty::All(vs, t), _) => {
    //             let free_vars = r.free_vars();
    //             t.instance_of(r) && vs.iter().all(|v| !free_vars.contains(v))
    //         }
    //         (_, Ty::All(_, t)) => {
    //             let sub = match self.mgu(t) {
    //                 Ok(s) => s,
    //                 _ => return false,
    //             };
    //             let t = t.clone().apply_subst(&sub);
    //             self.instance_of(&t)
    //         }
    //         (Ty::Qualified(p, t), Ty::Qualified(q, u)) => {
    //             p.iter()
    //                 .collect::<HashSet<_>>()
    //                 .is_superset(&q.iter().collect::<HashSet<_>>())
    //                 && t.instance_of(u)
    //         }
    //         (Ty::Qualified(_, t), u) => t.instance_of(u),
    //         (Ty::Func(p, q), Ty::Func(r, s)) if p.len() == r.len() => {
    //             p.iter().zip(r.iter()).all(|(x, y)| x.instance_of(y)) && q.instance_of(s)
    //         }
    //         (Ty::Projection(s, xs), Ty::Projection(t, ys)) if s == t && xs.len() == ys.len() => {
    //             xs.iter().zip(ys.iter()).all(|(x, y)| x.instance_of(y))
    //         }
    //         (Ty::Union(xs), Ty::Union(ys)) if xs.len() == ys.len() => {
    //             xs.iter().zip(ys.iter()).all(|(x, y)| x.instance_of(y))
    //         }
    //         (Ty::Cast(a, b), Ty::Cast(c, d)) => a.instance_of(c) && b.instance_of(d),
    //         (Ty::Var(_), Ty::Var(_)) => true,
    //         _ => self == r,
    //     }
    // }

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
        self.free_vars().len() != 0
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
        println!("unify: {} & {}", self, other);
        match (self, other) {
            (_, Ty::Any) | (_, Ty::Never) => Ok((f(Subst::new()), vec![])),
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
            (Ty::Qualified(p, s), Ty::Qualified(q, t)) if p == q => {
                Ok((f(Subst::new()), vec![g(s, t)]))
            }
            (Ty::Qualified(_, s), t) => s.unify_with(t, f, g),
            (s, Ty::Qualified(_, t)) => s.unify_with(t, f, g),
            (Ty::All(xs, s), Ty::All(ys, t)) if xs.len() == ys.len() => {
                Ok((f(Subst::new()), vec![g(s, t)]))
            }
            (Ty::All(xs, s), t) => s.unify_with(t, f, g),
            (s, Ty::All(xs, t)) => s.unify_with(t, f, g),
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
            (Ty::Projection(a, s), Ty::Projection(b, t)) => {
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

    pub fn is_func(&self) -> bool {
        match &self {
            Ty::All(_, ty) => ty.is_func(),
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
            Ty::All(xs, t) => {
                let mut vs: Vec<TyVar> = xs.clone();
                vs.extend(t.collect_tyvars());
                vs
            }
            Ty::Qualified(_, t) => t.collect_tyvars(),
            Ty::Func(param_tys, ret) => param_tys
                .iter()
                .chain(std::iter::once(ret.as_ref()))
                .flat_map(|t| t.collect_tyvars())
                .collect(),
            Ty::Var(v) => vec![v.clone()].into_iter().collect(),
            Ty::Union(t) | Ty::Projection(_, t) => {
                t.iter().flat_map(|t| t.collect_tyvars()).collect()
            }
            Ty::Cast(src, dst) => {
                let mut ty_vars = src.collect_tyvars();
                ty_vars.extend(dst.collect_tyvars());
                ty_vars
            }
            Ty::Bound(_) | Ty::Never | Ty::Any => vec![],
        };

        vs.dedup();
        vs
    }

    pub fn get_ty_params(&self) -> Vec<&Ty> {
        match self {
            Ty::All(_, t) => t.get_ty_params(),
            Ty::Qualified(_, t) => t.get_ty_params(),
            Ty::Cast(_, dst) => dst.get_ty_params(),
            Ty::Union(t) | Ty::Projection(_, t) => t.iter().collect(),
            Ty::Never | Ty::Any | Ty::Bound(_) | Ty::Var(_) | Ty::Func(_, _) => vec![],
        }
    }

    pub fn set_ty_params(self, tp: Vec<Ty>) -> Ty {
        match self {
            Ty::All(xs, t) => Ty::All(xs, Box::new(t.set_ty_params(tp))),
            Ty::Qualified(q, t) => Ty::Qualified(q, Box::new(t.set_ty_params(tp))),
            Ty::Cast(src, dst) => Ty::Cast(src, Box::new(dst.set_ty_params(tp))),
            Ty::Projection(s, _) => Ty::Projection(s, tp),
            t @ _ => t,
        }
    }

    pub fn get_ty_param_at(&self, idx: usize) -> &Ty {
        match self {
            Ty::All(_, t) => t.get_ty_param_at(idx),
            Ty::Qualified(_, t) => t.get_ty_param_at(idx),
            Ty::Cast(_, dst) => dst.get_ty_param_at(idx),
            Ty::Union(t) | Ty::Projection(_, t) => t.iter().nth(idx).unwrap(),
            Ty::Never | Ty::Any | Ty::Bound(_) | Ty::Var(_) | Ty::Func(_, _) => {
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

    pub fn try_unpack_fn(
        self,
    ) -> Result<(Option<Vec<TyVar>>, Vec<(String, Ty)>, Vec<Ty>, Ty), InferError> {
        if !self.is_func() {
            return Err(InferError {
                msg: format!("expected function type but found {}", self),
                src: vec![],
            });
        }

        match self {
            Ty::All(xs, ty) => {
                let (_, k, p, r) = ty.try_unpack_fn()?;
                Ok((Some(xs), k, p, r))
            }
            Ty::Func(p, r) => Ok((None, vec![], p, *r)),
            _ => unreachable!("attempted to unpack non-function: {:?}", self),
        }
    }
}

// #[cfg(test)]
// mod ty_tests {
//     use super::{Ty, TyVar};

//     #[test]
//     fn test_instanceof() {
//         let a = Ty::All(
//             vec![tvar!(a)],
//             Box::new(Ty::Projection(str!("A"), vec![Ty::Var(tvar!(a))])),
//         );
//         let b = Ty::Projection(str!("A"), vec![Ty::int()]);
//         assert!(b.instance_of(&a))
//     }
// }

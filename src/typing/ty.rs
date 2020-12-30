use std::{
    collections::{HashMap, HashSet},
    ops::BitOr,
    time::SystemTime,
};

use crate::{
    ast,
    utils::{join, map_join},
};

use super::{
    bound::{GreatestLowerBound, LeastUpperBound},
    constraint::ConstraintSet,
    context::Ctx,
    elim::Elim,
    generalize::Generalize,
    subst::{ApplySubst, Subst},
    variance::Variance,
    InferError,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TyVar(pub String);

impl std::fmt::Display for TyVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl TyVar {
    pub fn new() -> TyVar {
        let t = (SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
            % 100000000)
            / 10000;
        TyVar(format!("?t{}", t))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    Never,
    Any,
    IntLiteral,
    FloatLiteral,
    Var(TyVar),
    Union(Vec<Ty>),
    Func(Vec<Ty>, Box<Ty>),
    Projection(String, Vec<Ty>),
    Constrained(Vec<(String, Ty)>, Box<Ty>),
    All(Vec<TyVar>, Box<Ty>),
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Never => write!(f, "never"),
            Ty::Any => write!(f, "any"),
            Ty::IntLiteral => write!(f, "int literal"),
            Ty::FloatLiteral => write!(f, "float literal"),
            Ty::Var(v) => write!(f, "{}", v),
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
            Ty::Constrained(cts, t) => write!(
                f,
                "({{{}}}) in {}",
                map_join(cts, ", ", |(n, s)| { format!("({}): {}", n, s) }),
                t
            ),
            Ty::All(xs, t) => write!(f, "All[{}]({})", join(xs, ", "), t),
        }
    }
}

impl ApplySubst for Ty {
    fn apply_subst(self, subst: &Subst) -> Ty {
        match self {
            Ty::Any | Ty::Never | Ty::IntLiteral | Ty::FloatLiteral => self.clone(),
            Ty::Var(ref v) => subst.get(&v).cloned().unwrap_or_else(|| self.clone()),
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
            Ty::Constrained(cts, t) => {
                Ty::Constrained(cts.apply_subst(subst), Box::new(t.apply_subst(subst)))
            }
            Ty::All(xs, ty) => Ty::All(xs.clone(), Box::new(ty.apply_subst(subst))),
        }
    }
}

impl ApplySubst<Vec<Ty>> for Vec<Ty> {
    fn apply_subst(self, subst: &Subst) -> Vec<Ty> {
        self.into_iter().map(|x| x.apply_subst(subst)).collect()
    }
}

impl ApplySubst<Vec<(String, Ty)>> for Vec<(String, Ty)> {
    fn apply_subst(self, subst: &Subst) -> Vec<(String, Ty)> {
        self.into_iter()
            .map(|(n, t)| (n, t.apply_subst(subst)))
            .collect()
    }
}

impl Elim for Ty {
    /// S ⇑(V) T : T is the least supertype of S such that FV(T) ∩ V = ∅
    fn elim_up<T: Copy + Clone>(self, vs: &HashSet<&TyVar>) -> Result<Ty, InferError<T>> {
        Ok(match self {
            Ty::Any | Ty::Never | Ty::IntLiteral | Ty::FloatLiteral => self.clone(),
            Ty::Var(v) => {
                if !vs.contains(&v) {
                    Ty::Var(v.clone())
                } else {
                    Ty::Any
                }
            }
            Ty::Union(tys) => {
                let mut tys = tys.elim_up(vs)?;
                tys.dedup();
                if tys.len() == 1 {
                    tys.pop().unwrap()
                } else {
                    Ty::Union(tys)
                }
            }
            Ty::Projection(n, tys) => Ty::Projection(n, tys.elim_down(vs)?),
            Ty::Func(params, ret) => Ty::Func(params.elim_down(vs)?, Box::new(ret.elim_up(vs)?)),
            Ty::Constrained(cts, t) => Ty::Constrained(cts.elim_up(vs)?, Box::new(t.elim_up(vs)?)),
            Ty::All(xs, ty) => {
                for x in xs.iter() {
                    if vs.contains(&x) {
                        return Err(InferError {
                            msg: format!(
                                "could not find the least supertype of {:?}; {:?} exists as a bound variable",
                                ty, x
                            ),
                            metadata: None,
                        });
                    }
                }

                Ty::All(xs.clone(), Box::new(ty.elim_up(vs)?))
            }
        })
    }

    /// S ⇓(V) T : T is the greatest subtype of S such that FV(T) ∩ V = ∅
    fn elim_down<T: Copy + Clone>(self, vs: &HashSet<&TyVar>) -> Result<Ty, InferError<T>> {
        Ok(match self {
            Ty::Any | Ty::Never | Ty::IntLiteral | Ty::FloatLiteral => self.clone(),
            Ty::Var(v) => {
                if !vs.contains(&v) {
                    Ty::Var(v.clone())
                } else {
                    Ty::Never
                }
            }
            Ty::Union(tys) => {
                let mut tys = tys.elim_down(vs)?;
                tys.dedup();
                if tys.len() == 1 {
                    tys.pop().unwrap()
                } else {
                    Ty::Union(tys)
                }
            }
            Ty::Projection(n, tys) => Ty::Projection(n, tys.elim_up(vs)?),
            Ty::Func(params, ret) => Ty::Func(params.elim_up(vs)?, Box::new(ret.elim_down(vs)?)),
            Ty::Constrained(cts, t) => {
                Ty::Constrained(cts.elim_down(vs)?, Box::new(t.elim_down(vs)?))
            }
            Ty::All(xs, ty) => {
                for x in xs.iter() {
                    if vs.contains(&x) {
                        return Err(InferError {
                            msg: format!(
                                "could not find the greatest subtype of {:?}; {:?} exists as a bound variable",
                                ty, x
                            ),
                            metadata: None
                        });
                    }
                }
                let ty = ty.elim_down(vs)?;
                Ty::All(xs.clone(), Box::new(ty))
            }
        })
    }
}

impl Elim for Vec<Ty> {
    fn elim_up<T: Copy + Clone>(self, vs: &HashSet<&TyVar>) -> Result<Self, InferError<T>>
    where
        Self: Sized,
    {
        self.into_iter()
            .map(|p| p.elim_up(vs))
            .collect::<Result<Vec<_>, _>>()
    }

    fn elim_down<T: Copy + Clone>(self, vs: &HashSet<&TyVar>) -> Result<Self, InferError<T>>
    where
        Self: Sized,
    {
        self.into_iter()
            .map(|p| p.elim_down(vs))
            .collect::<Result<Vec<_>, _>>()
    }
}

impl Elim for Vec<(String, Ty)> {
    fn elim_up<T: Copy + Clone>(self, vs: &HashSet<&TyVar>) -> Result<Self, InferError<T>>
    where
        Self: Sized,
    {
        self.into_iter()
            .map(|(n, p)| Ok((n, p.elim_up(vs)?)))
            .collect::<Result<Vec<_>, _>>()
    }

    fn elim_down<T: Copy + Clone>(self, vs: &HashSet<&TyVar>) -> Result<Self, InferError<T>>
    where
        Self: Sized,
    {
        self.into_iter()
            .map(|(n, p)| Ok((n, p.elim_down(vs)?)))
            .collect::<Result<Vec<_>, _>>()
    }
}

impl LeastUpperBound for Ty {
    /// S ∨ T : least upper bound of S and T
    fn least_upper_bound(&self, t: &Ty) -> Ty {
        match (self, t) {
            (Ty::Projection(a, s), Ty::Projection(b, t)) if a == b => {
                Ty::Projection(a.clone(), s.greatest_lower_bound(t))
            }
            (Ty::Union(_), Ty::Union(_)) => unimplemented!("lub: union types"),
            (Ty::Func(vs, p), Ty::Func(ws, q)) if vs.len() == ws.len() => {
                let m = vs.greatest_lower_bound(ws);
                let j = p.least_upper_bound(q);
                Ty::Func(m, Box::new(j))
            }
            (Ty::All(xs, s), Ty::All(ys, t)) if xs == ys => {
                let u = s.least_upper_bound(t);
                Ty::All(xs.clone(), Box::new(u))
            }
            _ if self.is_subtype(t) => t.clone(),
            _ if t.is_subtype(self) => self.clone(),
            _ => Ty::Any,
        }
    }
}

impl LeastUpperBound for Vec<Ty> {
    fn least_upper_bound(&self, other: &Self) -> Self {
        self.iter()
            .zip(other.iter())
            .map(|(v, w)| v.least_upper_bound(w))
            .collect()
    }
}

impl GreatestLowerBound for Ty {
    /// S ∧ T: greatest lower bound of S and T
    fn greatest_lower_bound(&self, t: &Ty) -> Ty {
        match (self, t) {
            (Ty::Projection(a, s), Ty::Projection(b, t)) if a == b => {
                Ty::Projection(a.clone(), s.least_upper_bound(t))
            }
            (Ty::Union(_), Ty::Union(_)) => unimplemented!("glb: union types"),
            (Ty::Func(vs, p), Ty::Func(ws, q)) if vs.len() == ws.len() => {
                let m = vs.least_upper_bound(ws);
                let j = p.greatest_lower_bound(q);
                Ty::Func(m, Box::new(j))
            }
            (Ty::All(xs, s), Ty::All(ys, t)) if xs == ys => {
                let u = s.greatest_lower_bound(t);
                Ty::All(xs.clone(), Box::new(u))
            }
            _ if self.is_subtype(t) => self.clone(),
            _ if t.is_subtype(self) => t.clone(),
            _ => Ty::Never,
        }
    }
}

impl GreatestLowerBound for Vec<Ty> {
    fn greatest_lower_bound(&self, other: &Self) -> Self {
        self.iter()
            .zip(other.iter())
            .map(|(v, w)| v.greatest_lower_bound(w))
            .collect()
    }
}

impl Generalize for Ty {
    fn generalize(self, ty: Ty, reverse_subst: &mut HashMap<(Ty, Ty), TyVar>) -> Ty {
        println!("generalize: {} and {}", self, ty);
        if let Some(a) = reverse_subst.get(&(self.clone(), ty.clone())) {
            return Ty::Var(a.clone());
        }

        let ty = match (self, ty) {
            (Ty::Union(_), Ty::Union(_)) => unimplemented!("generalize unions"),
            (Ty::Union(tys), t) | (t, Ty::Union(tys)) => tys
                .into_iter()
                .fold(t, |s, t| s.generalize(t, reverse_subst)),
            (Ty::Constrained(tys, s), t) => {
                s.generalize(t, reverse_subst)
                // Ty::Constrained(tys, Box::new(s.generalize(t, reverse_subst)))
            }
            (s, Ty::Constrained(tys, t)) => {
                s.generalize(*t, reverse_subst)
                // Ty::Constrained(tys, Box::new(s.generalize(*t, reverse_subst)))
            }
            (Ty::Projection(a, s), Ty::Projection(b, t)) if a == b => {
                Ty::Projection(a.clone(), s.generalize(t, reverse_subst))
            }
            (Ty::Func(r, s), Ty::Func(t, u)) => {
                if r.len() == t.len() {
                    Ty::Func(
                        r.generalize(t, reverse_subst),
                        Box::new(s.generalize(*u, reverse_subst)),
                    )
                } else {
                    Ty::Union(vec![Ty::Func(r, s), Ty::Func(t, u)])
                }
            }
            (Ty::All(xs, s), t) => Ty::generalize_forall(xs, *s, t),
            (t, Ty::All(xs, s)) => Ty::generalize_forall(xs, *s, t),
            (a, b) => {
                if a != b {
                    let tv = TyVar::new();
                    reverse_subst.insert((a, b), tv.clone());
                    Ty::Var(tv)
                } else {
                    a
                }
            }
        };

        println!("generalized: {}", ty);

        ty
    }
}

impl Generalize for Vec<Ty> {
    fn generalize(self, other: Vec<Ty>, reverse_subst: &mut HashMap<(Ty, Ty), TyVar>) -> Vec<Ty> {
        self.into_iter()
            .zip(other.into_iter())
            .map(|(a, b)| a.generalize(b, reverse_subst))
            .collect()
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
    pub fn from_ast_ty(kind: &ast::TypeKind, scope: &ast::Path, ctx: &Ctx) -> Ty {
        match kind {
            ast::TypeKind::Unknown => unimplemented!(),
            ast::TypeKind::Basic {
                name,
                ty_params,
                bounds,
            } => {
                if let Some(ty) = ctx.get_var(name) {
                    ty.clone()
                } else {
                    Ty::Projection(name.to_string(), vec![])
                }
            }
            ast::TypeKind::Generic { name, bounds } => unimplemented!(),
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

    pub fn free_vars(&self) -> HashSet<&TyVar> {
        match self {
            Ty::All(xs, ty) => {
                let xs = xs.iter().collect();
                ty.free_vars().difference(&xs).map(|t| *t).collect()
            }
            Ty::Union(tys) | Ty::Projection(_, tys) => {
                tys.iter().flat_map(|t| t.free_vars()).collect()
            }
            Ty::Func(tys, r) => tys
                .iter()
                .chain(std::iter::once(r.as_ref()))
                .flat_map(|t| t.free_vars())
                .collect(),
            Ty::Var(tv) => vec![tv].into_iter().collect(),
            Ty::Constrained(_, t) => t.free_vars(),
            _ => HashSet::new(),
        }
    }

    pub fn generalize_forall(xs: Vec<TyVar>, s: Ty, t: Ty) -> Ty {
        // create fresh type variables
        let new_xs = (0..xs.len()).map(|_| TyVar::new()).collect::<Vec<_>>();
        let xs_subst = Subst::from_types(
            xs.clone(),
            new_xs
                .iter()
                .map(|x| Ty::Var(x.clone()))
                .collect::<Vec<_>>(),
        );

        // apply them to the types
        let s = s.apply_subst(&xs_subst);

        println!(
            "generalize for all: new_xs = {:?}; s = {}; t = {}",
            new_xs, s, t
        );
        let mut subst = HashMap::new();
        let original_ty = s;
        let u = original_ty.clone().generalize(t, &mut subst);
        println!("generalize for all: u = {}", u);

        if let Ty::Union(union_tys) = u {
            Ty::Union(
                union_tys
                    .into_iter()
                    .map(|t| {
                        if t == original_ty {
                            Ty::All(new_xs.clone(), Box::new(t))
                        } else {
                            t
                        }
                    })
                    .collect(),
            )
        } else {
            u
        }
    }

    /// Find a minimal substitution (σCR) will minimize R
    pub fn min_subst<T: Copy + Clone>(&self, cs: ConstraintSet) -> Result<Subst, InferError<T>> {
        let mut subst = Subst::new();
        // For each (S <: X[i] <: T) ∈ C:
        for (x, c) in cs.into_iter() {
            let (s, _, t) = c.unpack();
            let v = self.variance_in(&x);
            subst.as_mut().insert(
                x,
                match v {
                    // if R is constant or covariant in X[i] then σCR(X[i]) = S
                    Variance::Constant | Variance::Covariant => s,
                    // else if R is contravariant in X[i] then σCR(X[i]) = T
                    Variance::Contravariant => t,
                    // else if R is invariant in X[i] and S = T then σCR(X[i]) = S
                    Variance::Invariant if s == t => s,
                    // else σCR is undefined.
                    _ => {
                        return Err(InferError {
                            msg: format!("cannot find minimum subsitution for {:?}", self),
                            metadata: None,
                        })
                    }
                },
            );
        }

        Ok(subst)
    }

    pub fn variance_in(&self, v: &TyVar) -> Variance {
        match self {
            Ty::Any | Ty::Never | Ty::IntLiteral | Ty::FloatLiteral => Variance::Constant,
            Ty::Var(u) => {
                if v == u {
                    Variance::Covariant
                } else {
                    Variance::Constant
                }
            }
            Ty::Projection(_, tys) | Ty::Union(tys) => {
                if tys
                    .iter()
                    .find(|x| matches!(x, Ty::Var(u) if u == v))
                    .is_some()
                {
                    Variance::Covariant
                } else {
                    Variance::Constant
                }
            }
            Ty::Func(params, ret) => ret.variance_in(v).invert().concat(
                params
                    .iter()
                    .fold(Variance::Constant, |var, y| var.concat(y.variance_in(v))),
            ),
            Ty::Constrained(_, t) => t.variance_in(v),
            Ty::All(vs, ty) => {
                if vs.contains(v) {
                    ty.variance_in(v)
                } else {
                    Variance::Constant
                }
            }
        }
    }

    /// S <: T => S is a subtype of T
    pub fn is_subtype(&self, t: &Ty) -> bool {
        match (self, t) {
            (_, Ty::Any) | (Ty::Never, _) => true,
            (Ty::IntLiteral, t) if t.is_int_ty() => true,
            (Ty::FloatLiteral, t) if t.is_float_ty() => true,
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
            Ty::All(_, ty) | Ty::Constrained(_, ty) => ty.is_func(),
            Ty::Func(..) => true,
            _ => false,
        }
    }

    pub fn is_funcs_union(&self) -> bool {
        match &self {
            Ty::All(_, ty) | Ty::Constrained(_, ty) => ty.is_funcs_union(),
            Ty::Union(tys) => tys.iter().all(|t| t.is_func()),
            _ => false,
        }
    }

    pub fn is_union(&self) -> bool {
        match &self {
            Ty::All(_, ty) | Ty::Constrained(_, ty) => ty.is_union(),
            Ty::Union(_) => true,
            _ => false,
        }
    }

    pub fn is_tyvar(&self) -> bool {
        matches!(self, Ty::Var(_))
    }

    pub fn collect_tyvars(&self) -> HashSet<TyVar> {
        match self {
            Ty::All(xs, t) => {
                let mut unknowns: HashSet<TyVar> = xs.iter().cloned().collect();
                unknowns.extend(t.collect_tyvars());
                unknowns
            }
            Ty::Func(param_tys, ret) => param_tys
                .iter()
                .chain(std::iter::once(ret.as_ref()))
                .flat_map(|t| t.collect_tyvars())
                .collect(),
            Ty::Var(v) => vec![v.clone()].into_iter().collect(),
            _ => HashSet::new(),
        }
    }

    // pub fn collect_tyvars(&self) -> Vec<TyVar> {
    //     match self {
    //         Ty::Union(tys) | Ty::Projection(_, tys) => {
    //             tys.iter().flat_map(|t| t.free_vars()).cloned().collect()
    //         }
    //         Ty::Func(tys, r) => tys
    //             .iter()
    //             .chain(std::iter::once(r.as_ref()))
    //             .flat_map(|t| t.free_vars())
    //             .cloned()
    //             .collect(),
    //         Ty::Var(tv) => vec![tv.clone()].into_iter().collect(),
    //         Ty::All(_, ty) | Ty::Constrained(_, ty) => {
    //             ty.free_vars().into_iter().cloned().collect()
    //         }
    //         _ => vec![],
    //     }
    // }

    pub fn add_to_union(&mut self, ty: Ty) {
        if let Ty::All(_, t) = self {
            t.as_mut().add_to_union(ty);
        } else if let Ty::Union(tys) = self {
            tys.push(ty);
        }
    }

    pub fn get_constraints(self) -> Vec<(String, Ty)> {
        match self {
            Ty::Constrained(k, _) => k,
            _ => vec![],
        }
    }

    pub fn constrain_for(self, v: String, ty: Ty) -> Ty {
        match self {
            Ty::All(xs, t) => Ty::All(xs, Box::new(t.constrain_for(v, ty))),
            Ty::Constrained(mut k, t) => {
                k.push((v, ty));
                Ty::Constrained(k, t)
            }
            t => Ty::Constrained(vec![(v, ty)], Box::new(t)),
        }
    }

    pub fn unpack_constrained(self) -> (Option<Vec<TyVar>>, Option<Vec<(String, Ty)>>, Ty) {
        match self {
            Ty::All(xs, t) => {
                let (_, k, t) = t.unpack_constrained();
                (Some(xs), k, t)
            }
            Ty::Constrained(k, t) => (None, Some(k), *t),
            t => (None, None, t),
        }
    }

    pub fn try_unpack_overloaded_fn<T: Copy + Clone>(self) -> Result<Vec<Ty>, InferError<T>> {
        if !self.is_func() && !self.is_funcs_union() {
            return Err(InferError {
                msg: format!("expected function type but found {}", self),
                metadata: None,
            });
        }

        match self {
            Ty::Func(p, r) => Ok(vec![Ty::Func(p, r)]),
            Ty::All(xs, t) if t.is_func() => Ok(vec![Ty::All(xs, t)]),
            Ty::Constrained(k, t) if t.is_func() => Ok(vec![Ty::Constrained(k, t)]),
            Ty::Union(tys) => Ok(tys),
            t => unreachable!("attempted to unpack non-function: {:?}", t),
        }
    }

    pub fn try_unpack_fn<T: Copy + Clone>(
        self,
    ) -> Result<(Option<Vec<TyVar>>, Vec<(String, Ty)>, Vec<Ty>, Ty), InferError<T>> {
        if !self.is_func() {
            return Err(InferError {
                msg: format!("expected function type but found {}", self),
                metadata: None,
            });
        }

        match self {
            Ty::All(xs, ty) => {
                let (_, k, p, r) = ty.try_unpack_fn()?;
                Ok((Some(xs), k, p, r))
            }
            Ty::Constrained(k, ty) => {
                let (xs, _, p, r) = ty.try_unpack_fn()?;
                Ok((xs, k, p, r))
            }
            Ty::Func(p, r) => Ok((None, vec![], p, *r)),
            _ => unreachable!("attempted to unpack non-function: {:?}", self),
        }
    }
}

#[cfg(test)]
mod ty_test {
    use std::collections::HashMap;

    use crate::typing::Generalize;

    use super::{Ty, TyVar};

    #[test]
    fn test_generalize() {
        let t_int = || Ty::Projection("int".to_string(), vec![]);
        let t_float = || Ty::Projection("float".to_string(), vec![]);
        let t_char = || Ty::Projection("char".to_string(), vec![]);
        let t_bool = || Ty::Projection("bool".to_string(), vec![]);
        let t_seq = |x| Ty::Projection("seq".to_string(), vec![x]);

        let s = Ty::Func(vec![t_int(), t_int()], Box::new(t_int()));
        let t = Ty::Func(vec![t_int(), t_int()], Box::new(t_float()));
        let u = Ty::Func(vec![t_int(), t_float()], Box::new(t_float()));

        let mut subst = HashMap::new();
        let r = s.generalize(t, &mut subst).generalize(u, &mut subst);
        assert!(matches!(r, Ty::Func(..)));

        println!("generalized type: {}", r);

        let (_, _, params, ret) = r.try_unpack_fn::<()>().unwrap();
        assert_eq!(params.len(), 2);
        assert_eq!(params[0], t_int());
        assert!(matches!(params[1], Ty::Var(_)));
        assert!(matches!(ret, Ty::Var(_)));

        let lt_eq_ch = Ty::Func(vec![t_char(), t_char()], Box::new(t_bool()));
        let lt_eq_seq = Ty::All(
            vec![tvar!(a)],
            Box::new(Ty::Func(
                vec![t_seq(Ty::Var(tvar!(a))), t_seq(Ty::Var(tvar!(a)))],
                Box::new(t_bool()),
            )),
        );

        let mut subst = HashMap::new();
        let lt_eq = lt_eq_ch.generalize(lt_eq_seq, &mut subst);
        println!("generalized type for `≤`: {}", lt_eq);
        assert!(matches!(lt_eq, Ty::Func(..)));

        let (_, _, params, ret) = lt_eq.try_unpack_fn::<()>().unwrap();
        assert_eq!(params.len(), 2);
        assert_eq!(params[0], params[1]);
        assert_eq!(ret, t_bool());
    }
}

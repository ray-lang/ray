use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::{
    pathlib::{ItemPath, Path},
    ty::TyVar,
};

// Core type representation.
// This is intentionally minimal for now and will be extended to match
// docs/type-system.md as we go.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Ty {
    // Primitive types (ints, bools, etc.).
    Const(ItemPath),

    // Type variables (rigid or meta, distinguished by naming convention or
    // auxiliary maps for now).
    Var(TyVar),

    // Function types: (T0, T1, ...) -> Tn.
    Func(Vec<Ty>, Box<Ty>),

    // Pointer types.
    /// Shared reference `*T` — read-only, reference-counted (strong).
    Ref(Box<Ty>),
    /// Unique mutable reference `*mut T` — single-owner, non-copyable.
    MutRef(Box<Ty>),
    /// Identity reference `id *T` — weak reference, cannot access fields.
    IdRef(Box<Ty>),
    /// Raw pointer `rawptr[T]` — unsafe, no semantics.
    RawPtr(Box<Ty>),

    // Placeholder for other constructors: structs, traits, type constructors, etc.
    Proj(ItemPath, Vec<Ty>),

    // Product and array types.
    Tuple(Vec<Ty>),
    Array(Box<Ty>, usize),

    // Top type `any` (matches the existing system for now).
    Any,

    // Special bottom type `never`.
    #[default]
    Never,
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Never => write!(f, "never"),
            Ty::Any => write!(f, "any"),
            Ty::Const(p) => write!(f, "{}", p),
            Ty::Var(v) => write!(f, "{}", v.0),
            Ty::Func(params, ret) => {
                let parts = params
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({}) -> {}", parts, ret)
            }
            Ty::Ref(ty) => write!(f, "*{}", ty),
            Ty::MutRef(ty) => write!(f, "*mut {}", ty),
            Ty::IdRef(ty) => write!(f, "id *{}", ty),
            Ty::RawPtr(ty) => write!(f, "rawptr[{}]", ty),
            Ty::Proj(p, args) => {
                if args.is_empty() {
                    write!(f, "{}", p)
                } else {
                    let parts = args
                        .iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "{}[{}]", p, parts)
                }
            }
            Ty::Tuple(elems) => {
                let parts = elems
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", parts)
            }
            Ty::Array(ty, size) => {
                write!(f, "[{}; {}]", ty, size)
            }
        }
    }
}

impl Ty {
    /// Unit type `()`, represented as an empty tuple.
    #[inline(always)]
    pub fn unit() -> Self {
        Ty::Tuple(vec![])
    }

    /// Primitive `bool` type.
    #[inline(always)]
    pub fn bool() -> Self {
        Ty::Const("bool".into())
    }

    /// Primitive `int` type.
    #[inline(always)]
    pub fn int() -> Self {
        Ty::Const("int".into())
    }

    /// Primitive `float` type.
    #[inline(always)]
    pub fn float() -> Self {
        Ty::Const("float".into())
    }

    /// Primitive `string` type.
    #[inline(always)]
    pub fn string() -> Self {
        Ty::Const("string".into())
    }

    /// Primitive `bytes` (byte-string) type.
    #[inline(always)]
    pub fn bytes() -> Self {
        Ty::Const("bytes".into())
    }

    /// Primitive `byte` type.
    #[inline(always)]
    pub fn byte() -> Self {
        Ty::Const("byte".into())
    }

    /// Primitive `char` type.
    #[inline(always)]
    pub fn char() -> Self {
        Ty::Const("char".into())
    }

    /// Primitive `uint` type.
    #[inline(always)]
    pub fn uint() -> Self {
        Ty::Const("uint".into())
    }

    /// Nominal `nilable[T]` constructor, as used in the "Nilable literals"
    /// rules in docs/type-system.md.
    #[inline(always)]
    pub fn nilable(inner: Ty) -> Self {
        Ty::Proj("nilable".into(), vec![inner])
    }

    #[inline(always)]
    pub fn never() -> Self {
        Ty::Never
    }

    #[inline(always)]
    pub fn any() -> Self {
        Ty::Any
    }

    #[inline(always)]
    pub fn var(var: impl Into<Path>) -> Self {
        Ty::Var(TyVar(var.into()))
    }

    /// Helper to construct a function type `(params...) -> ret`.
    #[inline(always)]
    pub fn func(params: Vec<Ty>, ret: Ty) -> Self {
        Ty::Func(params, Box::new(ret))
    }

    pub fn tuple(elems: Vec<Ty>) -> Self {
        Ty::Tuple(elems)
    }

    pub fn array(elem: Ty, size: usize) -> Self {
        Ty::Array(Box::new(elem), size)
    }

    pub fn ref_of(ty: Ty) -> Self {
        Ty::Ref(Box::new(ty))
    }

    pub fn mut_ref_of(ty: Ty) -> Self {
        Ty::MutRef(Box::new(ty))
    }

    pub fn id_ref_of(ty: Ty) -> Self {
        Ty::IdRef(Box::new(ty))
    }

    pub fn rawptr(ty: Ty) -> Self {
        Ty::RawPtr(Box::new(ty))
    }

    pub fn list(ty: Ty) -> Self {
        Ty::Proj(ItemPath::from("list"), vec![ty])
    }

    pub fn range(ty: Ty) -> Self {
        Ty::Proj(ItemPath::from("range"), vec![ty])
    }

    pub fn con(path: impl Into<ItemPath>) -> Self {
        Ty::Const(path.into())
    }

    pub fn proj(path: impl Into<ItemPath>, args: Vec<Ty>) -> Self {
        Ty::Proj(path.into(), args)
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
    pub fn f32() -> Ty {
        Ty::con("f32")
    }

    #[inline(always)]
    pub fn f64() -> Ty {
        Ty::con("f64")
    }

    pub fn f128() -> Ty {
        Ty::con("f128")
    }

    /// Collect all free type variables appearing in this type.
    pub fn free_ty_vars(&self, out: &mut HashSet<TyVar>) {
        match self {
            Ty::Var(v) => {
                out.insert(v.clone());
            }
            Ty::Const(_) | Ty::Any | Ty::Never => {}
            Ty::Func(params, ret) => {
                for p in params {
                    p.free_ty_vars(out);
                }
                ret.free_ty_vars(out);
            }
            Ty::Ref(inner) | Ty::MutRef(inner) | Ty::IdRef(inner) | Ty::RawPtr(inner) => {
                inner.free_ty_vars(out);
            }
            Ty::Proj(_, args) | Ty::Tuple(args) => {
                for a in args {
                    a.free_ty_vars(out);
                }
            }
            Ty::Array(elem, _) => {
                elem.free_ty_vars(out);
            }
        }
    }

    pub fn with_vars(name: impl Into<ItemPath>, vars: &[TyVar]) -> Self {
        Ty::with_tys(name, vars.iter().map(|t| Ty::Var(t.clone())).collect())
    }

    pub fn with_tys(name: impl Into<ItemPath>, tys: Vec<Ty>) -> Self {
        if tys.is_empty() {
            Ty::Const(name.into())
        } else {
            Ty::Proj(name.into(), tys)
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
            "rawptr" => Ty::rawptr(Ty::Never),
            _ => return None,
        })
    }

    pub fn desc(&self) -> String {
        match self {
            Ty::Never => str!("never"),
            Ty::Any => str!("any"),
            Ty::Var(_) => str!("variable"),
            Ty::Tuple(_) => str!("tuple"),
            Ty::Ref(ty) => format!("shared reference to {}", ty.desc()),
            Ty::MutRef(ty) => format!("unique reference to {}", ty.desc()),
            Ty::IdRef(ty) => format!("identity reference to {}", ty.desc()),
            Ty::RawPtr(ty) => format!("raw pointer to {}", ty.desc()),
            Ty::Array(ty, _) => format!("array of {}", ty.desc()),
            Ty::Func(_, _) => str!("function"),
            Ty::Const(path) | Ty::Proj(path, _) => path.to_string(),
        }
    }

    /// Returns true if the name is a primitive/builtin type.
    ///
    /// These are types intrinsic to the type system with no struct definition.
    /// Note: `string` is NOT a primitive - it's a struct defined in core and
    /// made available via the prelude.
    pub fn is_builtin_name(name: &str) -> bool {
        match name {
            // Integer types
            "int" | "uint" | "i8" | "i16" | "i32" | "i64" | "i128" | "u8" | "u16" | "u32"
            | "u64" | "u128"
            // Float types
            | "float" | "f32" | "f64" | "f128"
            // Other primitives
            | "bool" | "char"
            // Builtin type constructors (no struct definition, intrinsic to the type system)
            | "nilable" | "type" => true,
            _ => false,
        }
    }

    pub fn ret_placeholder(path: impl Into<Path>) -> Ty {
        Ty::Var(TyVar(path.into().append("%r")))
    }

    #[inline(always)]
    pub fn ty_type(ty: Ty) -> Ty {
        Ty::Proj("type".into(), vec![ty])
    }

    #[inline(always)]
    pub fn is_builtin(&self) -> bool {
        match self {
            Ty::Const(name) => Ty::is_builtin_name(name.as_str()),
            _ => false,
        }
    }

    #[inline(always)]
    pub fn is_meta_ty(&self) -> bool {
        match self {
            Ty::Proj(fqn, _) => fqn.as_str() == "type",
            _ => false,
        }
    }

    /// Get the definition identity for lookups (nominal types only).
    ///
    /// Returns `Some(&ItemPath)` for `Const` and `Proj` types.
    /// Returns `None` for structural types (Ref, RawPtr, Tuple, Array, Func, Var, etc.).
    pub fn item_path(&self) -> Option<&ItemPath> {
        match self {
            Ty::Const(p) | Ty::Proj(p, _) => Some(p),
            _ => None,
        }
    }

    /// Create a nominal type (Const or Proj) from a path and optional type arguments.
    pub fn nominal(path: ItemPath, args: Vec<Ty>) -> Ty {
        if args.is_empty() {
            Ty::Const(path)
        } else {
            Ty::Proj(path, args)
        }
    }

    /// Mangle this type into a symbol-safe string for codegen.
    pub fn to_mangled(&self) -> String {
        match self {
            Ty::Const(path) => path.to_string(),
            Ty::Proj(path, args) => {
                if args.is_empty() {
                    path.to_string()
                } else {
                    let args_str = args
                        .iter()
                        .map(|t| t.to_mangled())
                        .collect::<Vec<_>>()
                        .join(",");
                    format!("{}[{}]", path, args_str)
                }
            }
            Ty::Var(v) => v.to_string(),
            Ty::Func(params, ret) => {
                let params_str = params
                    .iter()
                    .map(|t| t.to_mangled())
                    .collect::<Vec<_>>()
                    .join(",");
                format!("<({}):{}>", params_str, ret.to_mangled())
            }
            Ty::Ref(inner) => format!("*{}", inner.to_mangled()),
            Ty::MutRef(inner) => format!("*mut {}", inner.to_mangled()),
            Ty::IdRef(inner) => format!("id *{}", inner.to_mangled()),
            Ty::RawPtr(inner) => format!("rawptr[{}]", inner.to_mangled()),
            Ty::Tuple(elems) => {
                let elems_str = elems
                    .iter()
                    .map(|t| t.to_mangled())
                    .collect::<Vec<_>>()
                    .join(",");
                format!("({})", elems_str)
            }
            Ty::Array(elem, size) => format!("[{};{}]", elem.to_mangled(), size),
            Ty::Any => "any".to_string(),
            Ty::Never => "never".to_string(),
        }
    }

    /// Get the instantiated type path for codegen.
    ///
    /// Returns `Some(&ItemPath)` for nominal types
    ///
    /// Note: Prefer [`Ty::item_path`] instead
    pub fn get_path(&self) -> Path {
        match self {
            Ty::Never => Path::from("never"),
            Ty::Any => Path::from("any"),
            Ty::Var(v) => v.path().clone().into(),
            Ty::Const(item_path) => item_path.to_path(),
            Ty::Proj(item_path, params) => item_path.to_path().append_type_args(params.iter()),
            Ty::Array(ty, size) => {
                let base_path = Path::from("array");
                base_path.append_array_type(ty.as_ref().clone(), *size)
            }
            Ty::Ref(ty) => {
                let base_path = Path::from("ref");
                base_path.append_type_args(std::iter::once(ty.as_ref()))
            }
            Ty::MutRef(ty) => {
                let base_path = Path::from("mutref");
                base_path.append_type_args(std::iter::once(ty.as_ref()))
            }
            Ty::IdRef(ty) => {
                let base_path = Path::from("idref");
                base_path.append_type_args(std::iter::once(ty.as_ref()))
            }
            Ty::RawPtr(ty) => {
                let base_path = Path::from("rawptr");
                base_path.append_type_args(std::iter::once(ty.as_ref()))
            }
            Ty::Tuple(tys) => {
                let base_path = Path::from("tuple");
                base_path.append_type_args(tys.iter())
            }
            Ty::Func(_, _) => {
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
            Ty::Const(path) | Ty::Proj(path, _) => path.to_string(),
            Ty::Array(..) => str!("array"),
            Ty::Ref(_) => str!("ref"),
            Ty::MutRef(_) => str!("mutref"),
            Ty::IdRef(_) => str!("idref"),
            Ty::RawPtr(_) => str!("rawptr"),
            Ty::Func(_, _) => str!("func"),
        }
    }

    /// If this type is `nilable['a]`, return the payload type `'a`.
    pub fn nilable_payload(&self) -> Option<&Ty> {
        match self {
            Ty::Proj(head, params) => {
                if head.as_str() == "nilable" {
                    params.get(0)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, Ty::Tuple(elems) if elems.is_empty())
    }

    pub fn arity(&self) -> usize {
        match self {
            Ty::Any | Ty::Never | Ty::Const(_) | Ty::Var(_) => 0,
            Ty::Ref(_) | Ty::MutRef(_) | Ty::IdRef(_) | Ty::RawPtr(_) | Ty::Array(_, _) => 1,
            Ty::Proj(_, items) | Ty::Tuple(items) => items.len(),
            Ty::Func(items, _) => items.len() + 1,
        }
    }

    pub fn is_nullary(&self) -> bool {
        match self {
            Ty::Never | Ty::Any | Ty::Const(_) | Ty::Var(_) => true,
            Ty::Proj(_, tys) | Ty::Tuple(tys) => tys.len() == 0,
            Ty::Func(_, _)
            | Ty::Array(_, _)
            | Ty::Ref(_)
            | Ty::MutRef(_)
            | Ty::IdRef(_)
            | Ty::RawPtr(_) => false,
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

    #[inline(always)]
    pub fn is_tyvar(&self) -> bool {
        matches!(self, Ty::Var(_))
    }

    #[inline(always)]
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
            Ty::Tuple(tys) => tys.len() > 0,
            Ty::Array(_, _) | Ty::Proj(_, _) => true,
            _ => false,
        }
    }

    pub fn as_tyvar(self) -> TyVar {
        match self {
            Ty::Var(v) => v,
            _ => panic!("not a type variable"),
        }
    }

    pub fn get_func_param(&self, idx: usize) -> Option<&Ty> {
        match self {
            Ty::Func(params, _) => params.get(idx),
            _ => None,
        }
    }

    /// Returns all type arguments as references.
    ///
    /// For compound types, returns references to their inner types:
    /// - `Array[T]`, `Ref[T]`, `RawPtr[T]` → `[T]`
    /// - `Tuple[A, B]`, `Proj[A, B]` → `[A, B]`
    /// - Primitive types → `[]`
    ///
    /// See also [`type_params`](Self::type_params) which filters to only type variables.
    pub fn type_arguments(&self) -> Vec<&Ty> {
        match self {
            Ty::Array(t, _) | Ty::Ref(t) | Ty::MutRef(t) | Ty::IdRef(t) | Ty::RawPtr(t) => {
                vec![t.as_ref()]
            }
            Ty::Tuple(t) | Ty::Proj(_, t) => t.iter().collect(),
            Ty::Never | Ty::Any | Ty::Const(_) | Ty::Var(_) | Ty::Func(_, _) => vec![],
        }
    }

    /// Returns only type variable arguments (filters out concrete types).
    ///
    /// For `Proj` types like `Eq['a, int]`, returns only the type variable arguments `['a]`.
    /// For a bare `Var` type, returns that variable in a vec.
    /// For other types, returns an empty vec.
    ///
    /// See also [`type_arguments`](Self::type_arguments) which returns all type arguments.
    pub fn type_params(&self) -> Vec<TyVar> {
        match self {
            Ty::Proj(_, args) => args
                .iter()
                .filter_map(|t| {
                    if let Ty::Var(var) = t {
                        Some(var.clone())
                    } else {
                        None
                    }
                })
                .collect(),
            Ty::Var(var) => vec![var.clone()],
            _ => vec![],
        }
    }

    /// Returns the type argument at the given index, if it exists.
    ///
    /// For single-argument types (`Array`, `Ref`, `RawPtr`), only index 0 is valid.
    /// For multi-argument types (`Tuple`, `Proj`), returns the argument at that position.
    /// Returns `None` for types without arguments or invalid indices.
    pub fn type_argument_at(&self, idx: usize) -> Option<&Ty> {
        match self {
            Ty::Array(t, _) => {
                if idx != 0 {
                    return None;
                }

                Some(t.as_ref())
            }
            Ty::Ref(t) | Ty::MutRef(t) | Ty::IdRef(t) => {
                if idx != 0 {
                    return None;
                }

                Some(t.as_ref())
            }
            Ty::RawPtr(t) => {
                if idx != 0 {
                    return None;
                }

                Some(t.as_ref())
            }
            Ty::Tuple(t) | Ty::Proj(_, t) => Some(t.iter().nth(idx).unwrap()),
            Ty::Never | Ty::Any | Ty::Const(_) | Ty::Var(_) | Ty::Func(_, _) => None,
        }
    }

    /// Sets the type argument at the given index.
    ///
    /// # Panics
    /// Panics if the index is out of bounds or the type has no arguments.
    pub fn set_type_argument_at(&mut self, idx: usize, tp: Ty) {
        match self {
            Ty::Array(t, _) => {
                if idx != 0 {
                    panic!("array only has one type parameter: idx={}", idx)
                }

                *t = Box::new(tp);
            }
            Ty::Ref(t) | Ty::MutRef(t) | Ty::IdRef(t) => {
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
            Ty::Tuple(t) | Ty::Proj(_, t) => {
                t[idx] = tp;
            }
            Ty::Never | Ty::Any | Ty::Const(_) | Ty::Var(_) | Ty::Func(_, _) => {
                panic!("no type parameters: {}", self)
            }
        }
    }

    /// Returns the first type argument.
    ///
    /// # Panics
    /// Panics if the type has no arguments.
    #[inline(always)]
    pub fn first_type_argument(&self) -> &Ty {
        self.type_argument_at(0).unwrap()
    }

    pub fn try_borrow_fn(&self) -> Result<(&Vec<Ty>, &Ty), String> {
        match self {
            Ty::Func(params, ret) => Ok((params, ret)),
            _ => Err(format!("expected function type, found {}", self)),
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
            Ty::Ref(inner) | Ty::MutRef(inner) | Ty::IdRef(inner) | Ty::RawPtr(inner) => {
                Some(&inner)
            }
            _ => None,
        }
    }

    #[inline]
    pub fn is_any_pointer(&self) -> bool {
        matches!(
            self,
            Ty::Ref(_) | Ty::MutRef(_) | Ty::IdRef(_) | Ty::RawPtr(_)
        )
    }

    /// Returns true if this is a shared reference `*T`.
    #[inline]
    pub fn is_shared_ref(&self) -> bool {
        matches!(self, Ty::Ref(_))
    }

    /// Returns true if this is a unique mutable reference `*mut T`.
    #[inline]
    pub fn is_mut_ref(&self) -> bool {
        matches!(self, Ty::MutRef(_))
    }

    /// Returns true if this is an identity reference `id *T`.
    #[inline]
    pub fn is_id_ref(&self) -> bool {
        matches!(self, Ty::IdRef(_))
    }

    /// Returns true if this type contains `*mut T` anywhere in its structure.
    /// Used to reject `*mut T` in struct fields.
    pub fn contains_mut_ref(&self) -> bool {
        match self {
            Ty::MutRef(_) => true,
            Ty::Ref(inner) | Ty::IdRef(inner) | Ty::RawPtr(inner) | Ty::Array(inner, _) => {
                inner.contains_mut_ref()
            }
            Ty::Tuple(items) => items.iter().any(Ty::contains_mut_ref),
            Ty::Func(params, ret) => {
                params.iter().any(Ty::contains_mut_ref) || ret.contains_mut_ref()
            }
            Ty::Proj(_, args) => args.iter().any(Ty::contains_mut_ref),
            Ty::Never | Ty::Any | Ty::Var(_) | Ty::Const(_) => false,
        }
    }

    /// Returns true if this type contains an invalid reference nesting,
    /// such as `id *mut T` (identity reference to a mutable reference).
    pub fn contains_invalid_ref_nesting(&self) -> bool {
        match self {
            Ty::IdRef(inner) => inner.is_mut_ref() || inner.contains_invalid_ref_nesting(),
            Ty::Ref(inner) | Ty::MutRef(inner) | Ty::RawPtr(inner) | Ty::Array(inner, _) => {
                inner.contains_invalid_ref_nesting()
            }
            Ty::Tuple(items) => items.iter().any(Ty::contains_invalid_ref_nesting),
            Ty::Func(params, ret) => {
                params.iter().any(Ty::contains_invalid_ref_nesting)
                    || ret.contains_invalid_ref_nesting()
            }
            Ty::Proj(_, args) => args.iter().any(Ty::contains_invalid_ref_nesting),
            Ty::Never | Ty::Any | Ty::Var(_) | Ty::Const(_) => false,
        }
    }

    pub fn flatten(&self) -> Vec<&Ty> {
        match self {
            Ty::Never | Ty::Any | Ty::Var(_) | Ty::Const(_) => vec![self],
            Ty::Tuple(items) => items.iter().flat_map(Ty::flatten).collect(),
            Ty::Ref(ty) | Ty::MutRef(ty) | Ty::IdRef(ty) | Ty::RawPtr(ty) | Ty::Array(ty, _) => {
                ty.flatten()
            }
            Ty::Func(items, ty) => items
                .iter()
                .chain(std::iter::once(ty.as_ref()))
                .flat_map(Ty::flatten)
                .collect(),
            Ty::Proj(_, items) => std::iter::once(self)
                .chain(items.iter().flat_map(Ty::flatten))
                .collect(),
        }
    }

    /// Collect all unique user-written type variables from multiple types, recursively.
    /// Deduplicates by name, preserving discovery order.
    pub fn all_user_type_vars<'a>(types: impl Iterator<Item = &'a Ty>) -> Vec<TyVar> {
        let mut seen = HashSet::new();
        let mut out = Vec::new();
        for ty in types {
            for tv in ty.free_vars() {
                if tv.is_user_var() {
                    if let Some(name) = tv.path().name() {
                        if seen.insert(name) {
                            out.push(tv.clone());
                        }
                    }
                }
            }
        }
        out
    }

    /// Collect all unique type variables from this type in left-to-right traversal order.
    /// Deduplicates by name, preserving discovery order.
    pub fn unique_free_vars(&self) -> Vec<TyVar> {
        Ty::unique_free_vars_from(std::iter::once(self))
    }

    /// Collect all unique type variables from multiple types in left-to-right traversal order.
    /// Deduplicates by name, preserving discovery order.
    pub fn unique_free_vars_from<'a>(types: impl Iterator<Item = &'a Ty>) -> Vec<TyVar> {
        let mut seen = HashSet::new();
        let mut out = Vec::new();
        for ty in types {
            for tv in ty.free_vars() {
                if let Some(name) = tv.path().name() {
                    if seen.insert(name) {
                        out.push(tv.clone());
                    }
                }
            }
        }
        out
    }

    pub fn free_vars(&self) -> Vec<&TyVar> {
        match self {
            Ty::Never | Ty::Any | Ty::Const(_) => vec![],
            Ty::Var(v) => vec![v],
            Ty::Proj(_, tys) | Ty::Tuple(tys) => {
                tys.iter().map(|ty| ty.free_vars()).flatten().collect()
            }
            Ty::Ref(ty) | Ty::MutRef(ty) | Ty::IdRef(ty) | Ty::RawPtr(ty) | Ty::Array(ty, _) => {
                ty.free_vars()
            }
            Ty::Func(param_tys, ret_ty) => {
                let mut vars = param_tys
                    .iter()
                    .map(|ty| ty.free_vars())
                    .flatten()
                    .collect::<Vec<_>>();
                vars.extend(ret_ty.free_vars());
                vars
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ty::{Ty, TyVar};

    // --- Display ---

    #[test]
    fn display_mut_ref() {
        let ty = Ty::mut_ref_of(Ty::int());
        assert_eq!(ty.to_string(), "*mut int");
    }

    #[test]
    fn display_id_ref() {
        let ty = Ty::id_ref_of(Ty::int());
        assert_eq!(ty.to_string(), "id *int");
    }

    #[test]
    fn display_shared_ref() {
        let ty = Ty::ref_of(Ty::int());
        assert_eq!(ty.to_string(), "*int");
    }

    #[test]
    fn display_nested_mut_ref() {
        let ty = Ty::mut_ref_of(Ty::mut_ref_of(Ty::int()));
        assert_eq!(ty.to_string(), "*mut *mut int");
    }

    #[test]
    fn display_id_ref_of_shared_ref() {
        let ty = Ty::id_ref_of(Ty::ref_of(Ty::int()));
        assert_eq!(ty.to_string(), "id **int");
    }

    // --- Constructors ---

    #[test]
    fn mut_ref_of_wraps_inner_type() {
        let inner = Ty::string();
        let ty = Ty::mut_ref_of(inner.clone());
        assert_eq!(ty, Ty::MutRef(Box::new(inner)));
    }

    #[test]
    fn id_ref_of_wraps_inner_type() {
        let inner = Ty::string();
        let ty = Ty::id_ref_of(inner.clone());
        assert_eq!(ty, Ty::IdRef(Box::new(inner)));
    }

    // --- Predicates ---

    #[test]
    fn is_shared_ref_only_matches_ref() {
        assert!(Ty::ref_of(Ty::int()).is_shared_ref());
        assert!(!Ty::mut_ref_of(Ty::int()).is_shared_ref());
        assert!(!Ty::id_ref_of(Ty::int()).is_shared_ref());
        assert!(!Ty::int().is_shared_ref());
    }

    #[test]
    fn is_mut_ref_only_matches_mut_ref() {
        assert!(Ty::mut_ref_of(Ty::int()).is_mut_ref());
        assert!(!Ty::ref_of(Ty::int()).is_mut_ref());
        assert!(!Ty::id_ref_of(Ty::int()).is_mut_ref());
        assert!(!Ty::int().is_mut_ref());
    }

    #[test]
    fn is_id_ref_only_matches_id_ref() {
        assert!(Ty::id_ref_of(Ty::int()).is_id_ref());
        assert!(!Ty::ref_of(Ty::int()).is_id_ref());
        assert!(!Ty::mut_ref_of(Ty::int()).is_id_ref());
        assert!(!Ty::int().is_id_ref());
    }

    #[test]
    fn is_any_pointer_includes_all_ref_types() {
        assert!(Ty::ref_of(Ty::int()).is_any_pointer());
        assert!(Ty::mut_ref_of(Ty::int()).is_any_pointer());
        assert!(Ty::id_ref_of(Ty::int()).is_any_pointer());
        assert!(Ty::RawPtr(Box::new(Ty::int())).is_any_pointer());
        assert!(!Ty::int().is_any_pointer());
    }

    // --- unwrap_pointer ---

    #[test]
    fn unwrap_pointer_works_for_all_ref_types() {
        assert_eq!(Ty::ref_of(Ty::int()).unwrap_pointer(), Some(&Ty::int()));
        assert_eq!(Ty::mut_ref_of(Ty::int()).unwrap_pointer(), Some(&Ty::int()));
        assert_eq!(Ty::id_ref_of(Ty::int()).unwrap_pointer(), Some(&Ty::int()));
        assert_eq!(
            Ty::RawPtr(Box::new(Ty::int())).unwrap_pointer(),
            Some(&Ty::int())
        );
        assert_eq!(Ty::int().unwrap_pointer(), None);
    }

    // --- arity & type_arguments ---

    #[test]
    fn arity_is_one_for_all_ref_types() {
        assert_eq!(Ty::ref_of(Ty::int()).arity(), 1);
        assert_eq!(Ty::mut_ref_of(Ty::int()).arity(), 1);
        assert_eq!(Ty::id_ref_of(Ty::int()).arity(), 1);
    }

    #[test]
    fn type_arguments_returns_inner_for_all_ref_types() {
        assert_eq!(Ty::ref_of(Ty::int()).type_arguments(), vec![&Ty::int()]);
        assert_eq!(Ty::mut_ref_of(Ty::int()).type_arguments(), vec![&Ty::int()]);
        assert_eq!(Ty::id_ref_of(Ty::int()).type_arguments(), vec![&Ty::int()]);
    }

    // --- desc ---

    #[test]
    fn desc_for_ref_types() {
        assert_eq!(Ty::ref_of(Ty::int()).desc(), "shared reference to int");
        assert_eq!(Ty::mut_ref_of(Ty::int()).desc(), "unique reference to int");
        assert_eq!(Ty::id_ref_of(Ty::int()).desc(), "identity reference to int");
    }

    // --- free_vars ---

    #[test]
    fn free_vars_traverses_mut_ref() {
        let var = TyVar::new("'a");
        let ty = Ty::mut_ref_of(Ty::Var(var.clone()));
        let vars = ty.free_vars();
        assert_eq!(vars.len(), 1);
        assert_eq!(*vars[0], var);
    }

    #[test]
    fn free_vars_traverses_id_ref() {
        let var = TyVar::new("'a");
        let ty = Ty::id_ref_of(Ty::Var(var.clone()));
        let vars = ty.free_vars();
        assert_eq!(vars.len(), 1);
        assert_eq!(*vars[0], var);
    }

    // --- Equality: different ref kinds are NOT equal ---

    #[test]
    fn ref_kinds_are_distinct() {
        let shared = Ty::ref_of(Ty::int());
        let mutable = Ty::mut_ref_of(Ty::int());
        let identity = Ty::id_ref_of(Ty::int());

        assert_ne!(shared, mutable);
        assert_ne!(shared, identity);
        assert_ne!(mutable, identity);
    }

    // --- to_mangled ---

    #[test]
    fn to_mangled_for_ref_types() {
        let shared = Ty::ref_of(Ty::int()).to_mangled();
        let mutable = Ty::mut_ref_of(Ty::int()).to_mangled();
        let identity = Ty::id_ref_of(Ty::int()).to_mangled();

        // Each should produce a distinct mangled name
        assert_ne!(shared, mutable);
        assert_ne!(shared, identity);
        assert_ne!(mutable, identity);

        assert!(mutable.contains("mut"));
        assert!(identity.contains("id"));
    }

    // --- contains_mut_ref ---

    #[test]
    fn contains_mut_ref_direct() {
        assert!(Ty::mut_ref_of(Ty::int()).contains_mut_ref());
    }

    #[test]
    fn contains_mut_ref_nested_in_ref() {
        // *(*mut int) — shared ref containing mut ref
        assert!(Ty::ref_of(Ty::mut_ref_of(Ty::int())).contains_mut_ref());
    }

    #[test]
    fn contains_mut_ref_nested_in_id_ref() {
        // id *(*mut int)
        assert!(Ty::id_ref_of(Ty::mut_ref_of(Ty::int())).contains_mut_ref());
    }

    #[test]
    fn contains_mut_ref_in_tuple() {
        let ty = Ty::Tuple(vec![Ty::int(), Ty::mut_ref_of(Ty::string())]);
        assert!(ty.contains_mut_ref());
    }

    #[test]
    fn contains_mut_ref_in_func_param() {
        let ty = Ty::Func(vec![Ty::mut_ref_of(Ty::int())], Box::new(Ty::bool()));
        assert!(ty.contains_mut_ref());
    }

    #[test]
    fn contains_mut_ref_negative() {
        assert!(!Ty::int().contains_mut_ref());
        assert!(!Ty::ref_of(Ty::int()).contains_mut_ref());
        assert!(!Ty::id_ref_of(Ty::int()).contains_mut_ref());
        assert!(!Ty::ref_of(Ty::ref_of(Ty::int())).contains_mut_ref());
    }

    // --- contains_invalid_ref_nesting ---

    #[test]
    fn contains_invalid_ref_nesting_id_mut() {
        // id *mut int — identity ref directly wrapping mut ref
        assert!(Ty::id_ref_of(Ty::mut_ref_of(Ty::int())).contains_invalid_ref_nesting());
    }

    #[test]
    fn contains_invalid_ref_nesting_deep() {
        // Tuple containing id *mut int
        let ty = Ty::Tuple(vec![Ty::int(), Ty::id_ref_of(Ty::mut_ref_of(Ty::string()))]);
        assert!(ty.contains_invalid_ref_nesting());
    }

    #[test]
    fn contains_invalid_ref_nesting_negative() {
        // id *int — valid
        assert!(!Ty::id_ref_of(Ty::int()).contains_invalid_ref_nesting());
        // id **int — valid (id ref to shared ref)
        assert!(!Ty::id_ref_of(Ty::ref_of(Ty::int())).contains_invalid_ref_nesting());
        // *mut int — valid (not nesting issue)
        assert!(!Ty::mut_ref_of(Ty::int()).contains_invalid_ref_nesting());
        // *int — valid
        assert!(!Ty::ref_of(Ty::int()).contains_invalid_ref_nesting());
    }
}

use std::collections::{HashMap, HashSet};
use std::fmt::write;
use std::ops::{Deref, DerefMut};

use serde::{Deserialize, Serialize};

use ray_shared::collections::{namecontext::NameContext, nametree::Scope};
use ray_shared::pathlib::Path;
use ray_shared::span::Source;
use ray_shared::str;

use crate::constraints::Predicate;
use crate::{TypeError, info::TypeSystemInfo, tyctx::TyCtx, unify::mgu};

pub const SCHEMA_PREFIX: &'static str = "?s";
pub const SKOLEM_PREFIX: &'static str = "?k";

/// Shared allocator for schema variables (`?sN`).
///
/// Both the frontend lowering context and the solver need to mint fresh
/// schema variables, so we keep the allocator tiny and share it via `Rc`.
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct SchemaVarAllocator {
    next_id: u32,
}

impl SchemaVarAllocator {
    pub fn new() -> Self {
        SchemaVarAllocator { next_id: 0 }
    }

    pub fn alloc(&mut self) -> TyVar {
        let name = format!("{}{}", SCHEMA_PREFIX, self.next_id);
        self.next_id += 1;
        TyVar::new(name)
    }

    pub fn curr_id(&self) -> u32 {
        self.next_id
    }
}

// Global substitution map for type variables.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Subst(HashMap<TyVar, Ty>);

impl Deref for Subst {
    type Target = HashMap<TyVar, Ty>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Subst {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl IntoIterator for Subst {
    type Item = (TyVar, Ty);

    type IntoIter = std::collections::hash_map::IntoIter<TyVar, Ty>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<(TyVar, Ty)> for Subst {
    fn from_iter<T: IntoIterator<Item = (TyVar, Ty)>>(iter: T) -> Self {
        let mut subst = Subst::new();
        for (k, v) in iter {
            subst.insert(k, v);
        }
        subst
    }
}

impl std::fmt::Display for Subst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            return write!(f, "{{}}");
        }

        if f.alternate() {
            write!(f, "{{\n")?;
        } else {
            write!(f, "{{")?;
        }

        let mut lines = self.iter().collect::<Vec<_>>();
        lines.sort_by_key(|(var, _)| *var);

        let mut i = 0;
        for (var, ty) in lines {
            if f.alternate() {
                write!(f, "  {}: {}\n", var, ty)?;
            } else {
                if i != 0 {
                    write!(f, ",")?;
                }
                write!(f, " {}: {}", var, ty)?;
            }
            i += 1;
        }

        if f.alternate() {
            write!(f, "}}")
        } else {
            write!(f, " }}")
        }
    }
}

impl Subst {
    pub fn new() -> Self {
        Subst(HashMap::new())
    }

    pub fn union(&mut self, other: Subst) {
        for (_, ty) in self.iter_mut() {
            ty.apply_subst(&other);
        }

        for (var, ty) in other {
            if !self.contains_key(&var) {
                self.insert(var, ty);
            }
        }
    }
}

/// Trait for values that can have a type substitution applied to them.
pub trait Substitutable {
    fn apply_subst(&mut self, subst: &Subst);
}

impl<T> Substitutable for Option<T>
where
    T: Substitutable,
{
    fn apply_subst(&mut self, subst: &Subst) {
        if let Some(inner) = self {
            inner.apply_subst(subst);
        }
    }
}

impl<T> Substitutable for Vec<T>
where
    T: Substitutable,
{
    fn apply_subst(&mut self, subst: &Subst) {
        for ty in self.iter_mut() {
            ty.apply_subst(subst);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct TyVar(pub Path);

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

    /// Returns true if this variable name looks like a "meta" variable
    /// (e.g. "?t0"), following the current naming convention. We also
    /// treat schema variables (e.g. "?s0") and return-placeholders
    /// (e.g. "%r0") as metas so they can participate in unification and
    /// be solved like other unknowns.
    pub fn is_meta(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            return name.starts_with("?") || name.starts_with("%r");
        }
        false
    }

    /// Returns true if this variable is used as a placeholder for a return
    /// type in the current naming scheme (e.g. "%r0").
    pub fn is_ret_placeholder(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            return name.starts_with("%r");
        }
        false
    }

    /// Returns true if this variable name is some form of unknown (any name
    /// starting with "?").
    pub fn is_unknown(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            return name.starts_with("?");
        }
        false
    }

    /// Returns true if this variable name represents a skolem introduced
    /// during annotation checking (currently `{SKOLEM_PREFIX}*`).
    pub fn is_skolem(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            return name.starts_with(SKOLEM_PREFIX);
        }
        false
    }

    /// Returns true if this variable name represents a schema variable
    pub fn is_schema(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            return name.starts_with(SCHEMA_PREFIX);
        }
        false
    }
}

impl Substitutable for TyVar {
    fn apply_subst(&mut self, subst: &Subst) {
        if let Some(Ty::Var(var)) = subst.get(self) {
            *self = var.clone();
        }
    }
}

impl std::fmt::Display for TyVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&str> for TyVar {
    fn from(value: &str) -> Self {
        TyVar(value.into())
    }
}

impl Default for TyVar {
    fn default() -> Self {
        Self(Default::default())
    }
}

// Core type representation.
// This is intentionally minimal for now and will be extended to match
// docs/type-system.md as we go.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Ty {
    // Primitive types (ints, bools, etc.).
    Const(Path),

    // Type variables (rigid or meta, distinguished by naming convention or
    // auxiliary maps for now).
    Var(TyVar),

    // Function types: (T0, T1, ...) -> Tn.
    Func(Vec<Ty>, Box<Ty>),

    // Pointer types: *T and rawptr[T] and similar will be refined later.
    Ref(Box<Ty>),
    RawPtr(Box<Ty>),

    // Placeholder for other constructors: structs, traits, type constructors, etc.
    Proj(Path, Vec<Ty>),

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

impl Substitutable for Ty {
    fn apply_subst(&mut self, subst: &Subst) {
        match self {
            Ty::Var(v) => {
                if let Some(t) = subst.get(v) {
                    *self = t.clone();
                    // Chase chains if necessary.
                    self.apply_subst(subst);
                }
            }
            Ty::Const(_) | Ty::Any | Ty::Never => {}
            Ty::Func(params, ret) => {
                for p in params {
                    p.apply_subst(subst);
                }
                ret.apply_subst(subst);
            }
            Ty::Ref(inner) | Ty::RawPtr(inner) => {
                inner.apply_subst(subst);
            }
            Ty::Proj(_, args) | Ty::Tuple(args) => {
                for a in args {
                    a.apply_subst(subst);
                }
            }
            Ty::Array(elem, _) => {
                elem.apply_subst(subst);
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

    pub fn rawptr(ty: Ty) -> Self {
        Ty::RawPtr(Box::new(ty))
    }

    pub fn list(ty: Ty) -> Self {
        Ty::Proj(Path::from("list"), vec![ty])
    }

    pub fn range(ty: Ty) -> Self {
        Ty::Proj(Path::from("range"), vec![ty])
    }

    pub fn con(path: impl Into<Path>) -> Self {
        Ty::Const(path.into())
    }

    pub fn proj(path: impl Into<Path>, args: Vec<Ty>) -> Self {
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
            Ty::Ref(inner) | Ty::RawPtr(inner) => {
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

    pub fn with_vars(name: impl Into<Path>, vars: &[TyVar]) -> Self {
        Ty::with_tys(name, vars.iter().map(|t| Ty::Var(t.clone())).collect())
    }

    pub fn with_tys(name: impl Into<Path>, tys: Vec<Ty>) -> Self {
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
            Ty::Ref(ty) => format!("reference to {}", ty.desc()),
            Ty::RawPtr(ty) => format!("raw pointer to {}", ty.desc()),
            Ty::Array(ty, _) => format!("array of {}", ty.desc()),
            Ty::Func(_, _) => str!("function"),
            Ty::Const(path) | Ty::Proj(path, _) => path.to_string(),
        }
    }

    pub fn resolve_fqns(&mut self, scopes: &Vec<Scope>, ncx: &NameContext) {
        fn resolve_fqn(path: &mut Path, scopes: &Vec<Scope>, ncx: &NameContext) {
            let name = path.to_short_name();
            if Ty::is_builtin_name(&name) {
                return;
            }

            if let Some(fqn) = ncx.resolve_name(scopes, &name) {
                log::debug!("[resolve_fqns] resolved name: {} -> {:?}", name, fqn);
                *path = fqn;
            } else {
                log::debug!(
                    "[resolve_fqns] COULD NOT RESOLVE NAME {} in scopes = {:?}",
                    name,
                    scopes
                )
            }
        }

        match self {
            Ty::Const(path) => {
                resolve_fqn(path, scopes, ncx);
            }
            Ty::Proj(path, tys) => {
                resolve_fqn(path, scopes, ncx);
                for ty in tys {
                    ty.resolve_fqns(scopes, ncx);
                }
            }
            Ty::Tuple(tys) => {
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
                    let mapped_tv = tcx.new_schema_var();
                    tcx.add_var_mapping(tv.clone(), mapped_tv.clone());
                    mapped_tv
                };
            }
            Ty::Tuple(tys) => {
                tys.iter_mut().for_each(|t| t.map_vars(tcx));
            }
            Ty::Proj(_, param_tys) => {
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

    pub fn ret_placeholder(path: impl Into<Path>) -> Ty {
        Ty::Var(TyVar(path.into().append("%r")))
    }

    #[inline(always)]
    pub fn ty_type(ty: Ty) -> Ty {
        Ty::Proj(str!("type").into(), vec![ty])
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

    pub fn get_path(&self) -> Path {
        match self {
            Ty::Never => Path::from("never"),
            Ty::Any => Path::from("any"),
            Ty::Var(v) => v.path().clone(),
            Ty::Const(s) => Path::from(s.clone()),
            Ty::Proj(base_path, params) => base_path.append_type_args(params.iter()),
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
            Ty::Array(..) | Ty::Ref(_) | Ty::RawPtr(_) | Ty::Func(_, _) => {
                str!("")
            }
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
            Ty::Ref(_) | Ty::RawPtr(_) | Ty::Array(_, _) => 1,
            Ty::Proj(_, items) | Ty::Tuple(items) => items.len(),
            Ty::Func(items, _) => items.len() + 1,
        }
    }

    pub fn is_nullary(&self) -> bool {
        match self {
            Ty::Never | Ty::Any | Ty::Const(_) | Ty::Var(_) => true,
            Ty::Proj(_, tys) | Ty::Tuple(tys) => tys.len() == 0,
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

    pub fn nominal_kind(&self, tcx: &TyCtx) -> Option<NominalKind> {
        let fqn = self.get_path().with_names_only();
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
            Ty::Func(params, _) => params.get(idx),
            _ => None,
        }
    }

    pub fn get_ty_params(&self) -> Vec<&Ty> {
        match self {
            Ty::Array(t, _) | Ty::Ref(t) | Ty::RawPtr(t) => vec![t.as_ref()],
            Ty::Tuple(t) | Ty::Proj(_, t) => t.iter().collect(),
            Ty::Never | Ty::Any | Ty::Const(_) | Ty::Var(_) | Ty::Func(_, _) => vec![],
        }
    }

    pub fn get_ty_param_at(&self, idx: usize) -> Option<&Ty> {
        match self {
            Ty::Array(t, _) => {
                if idx != 0 {
                    return None;
                }

                Some(t.as_ref())
            }
            Ty::Ref(t) => {
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
            Ty::Tuple(t) | Ty::Proj(_, t) => {
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

    pub fn try_borrow_fn(&self) -> Result<(&Vec<Ty>, &Ty), TypeError> {
        match self {
            Ty::Func(params, ret) => Ok((params, ret)),
            _ => Err(TypeError::message(
                format!("expected function type, found {}", self),
                TypeSystemInfo::default(),
            )),
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

    pub fn flatten(&self) -> Vec<&Ty> {
        match self {
            Ty::Never | Ty::Any | Ty::Var(_) | Ty::Const(_) => vec![self],
            Ty::Tuple(items) => items.iter().flat_map(Ty::flatten).collect(),
            Ty::Ref(ty) | Ty::RawPtr(ty) | Ty::Array(ty, _) => ty.flatten(),
            Ty::Func(items, ty) => items
                .iter()
                .chain(std::iter::once(ty.as_ref()))
                .flat_map(Ty::flatten)
                .collect(),
            Ty::Proj(_, items) => items.iter().flat_map(Ty::flatten).collect(),
        }
    }

    pub fn free_vars(&self) -> Vec<&TyVar> {
        match self {
            Ty::Never | Ty::Any | Ty::Const(_) => vec![],
            Ty::Var(v) => vec![v],
            Ty::Proj(_, tys) | Ty::Tuple(tys) => {
                tys.iter().map(|ty| ty.free_vars()).flatten().collect()
            }
            Ty::Ref(ty) | Ty::RawPtr(ty) | Ty::Array(ty, _) => ty.free_vars(),
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

// Simple type scheme wrapper: forall vars. qualifiers => ty
// This follows the spec's treatment of generalized types with attached
// residual predicates.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TyScheme {
    pub vars: Vec<TyVar>,
    /// Qualifiers / residual predicates attached to this scheme.
    pub qualifiers: Vec<Predicate>,
    pub ty: Ty,
}

impl std::fmt::Display for TyScheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.vars.is_empty() {
            let vars = self
                .vars
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            write!(f, "forall[{}]. ", vars)?;
        }
        if !self.qualifiers.is_empty() {
            let quals = self
                .qualifiers
                .iter()
                .map(|q| q.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            write!(f, "{} => ", quals)?;
        }

        write!(f, "{}", self.ty)
    }
}

impl Substitutable for TyScheme {
    fn apply_subst(&mut self, subst: &Subst) {
        self.ty.apply_subst(subst);
        for q in &mut self.qualifiers {
            q.apply_subst(subst);
        }
    }
}

impl From<Ty> for TyScheme {
    fn from(ty: Ty) -> Self {
        TyScheme::from_mono(ty)
    }
}

impl TyScheme {
    pub fn from_mono(ty: Ty) -> Self {
        TyScheme {
            vars: Vec::new(),
            qualifiers: Vec::new(),
            ty,
        }
    }

    pub fn from_var(var: TyVar) -> Self {
        TyScheme::from_mono(Ty::Var(var))
    }

    pub fn new(vars: Vec<TyVar>, qualifiers: Vec<Predicate>, ty: Ty) -> Self {
        TyScheme {
            vars,
            qualifiers,
            ty,
        }
    }

    pub fn scheme(_scheme: TyScheme) -> Self {
        todo!("TyScheme::scheme is not yet implemented");
    }

    pub fn qualifiers(&self) -> &[Predicate] {
        &self.qualifiers
    }

    pub fn qualifiers_mut(&mut self) -> &mut Vec<Predicate> {
        &mut self.qualifiers
    }

    pub fn mono(&self) -> &Ty {
        &self.ty
    }

    pub fn mono_mut(&mut self) -> &mut Ty {
        &mut self.ty
    }

    pub fn into_mono(self) -> Ty {
        self.ty
    }

    pub fn has_quantifiers(&self) -> bool {
        !self.vars.is_empty()
    }

    pub fn has_freevars(&self) -> bool {
        todo!("TyScheme::has_freevars is not yet implemented");
    }

    pub fn is_polymorphic(&self) -> bool {
        self.has_quantifiers()
    }

    pub fn quantifiers(&self) -> &Vec<TyVar> {
        &self.vars
    }

    pub fn is_unit(&self) -> bool {
        self.ty.is_unit()
    }

    pub fn take(self) -> TyScheme {
        todo!("TyScheme::take is not yet implemented");
    }

    pub fn try_borrow_fn(&self) -> Option<(&Vec<TyVar>, &Vec<Predicate>, &Vec<Ty>, &Ty)> {
        match &self.ty {
            Ty::Func(params, ret) => Some((&self.vars, &self.qualifiers, params, ret)),
            _ => None,
        }
    }

    pub fn resolve_fqns(&mut self, scopes: &Vec<Scope>, ncx: &NameContext) {
        for pred in self.qualifiers_mut().iter_mut() {
            match pred {
                Predicate::Class(p) => {
                    for ty in p.args.iter_mut() {
                        ty.resolve_fqns(scopes, ncx);
                    }
                }
                Predicate::HasField(p) => {
                    p.record_ty.resolve_fqns(scopes, ncx);
                    p.field_ty.resolve_fqns(scopes, ncx);
                }
                Predicate::Recv(p) => {
                    p.recv_ty.resolve_fqns(scopes, ncx);
                    p.expr_ty.resolve_fqns(scopes, ncx);
                }
            }
        }

        self.mono_mut().resolve_fqns(scopes, ncx);
    }

    pub fn flatten(&self) -> Vec<&Ty> {
        todo!("TyScheme::flatten is not yet implemented");
    }

    pub fn instantiate_fn_with_args(
        &mut self,
        poly_ty: Option<&mut TyScheme>,
        arg_tys: &mut [TyScheme],
    ) -> Subst {
        let mut accumulated = Subst::new();
        let func_params = match &self.ty {
            Ty::Func(params, _) => params.clone(),
            _ => return accumulated,
        };

        let mut poly_ref = poly_ty;
        let arg_len = arg_tys.len();

        for (idx, param_ty) in func_params.iter().enumerate() {
            if idx >= arg_len {
                break;
            }

            let arg_ty = arg_tys[idx].mono().clone();
            let Ok((_, subst_chunk)) = mgu(param_ty, &arg_ty) else {
                continue;
            };

            self.apply_subst(&subst_chunk);
            for arg in arg_tys.iter_mut() {
                arg.apply_subst(&subst_chunk);
            }
            if let Some(poly) = poly_ref.as_mut() {
                poly.apply_subst(&subst_chunk);
            }

            for (var, ty) in subst_chunk.into_iter() {
                accumulated.insert(var, ty);
            }
        }

        // remove the variables that are no longer referenced in both `self` and `poly_ref`
        let mut free = HashSet::new();
        self.free_ty_vars(&mut free);
        log::debug!("free vars: {:?}", free);
        log::debug!("vars before: {:?}", self.vars);
        self.vars.retain(|var| free.contains(var));
        log::debug!("vars after: {:?}", self.vars);

        if let Some(poly) = poly_ref {
            poly.vars.retain(|var| free.contains(var));
        }

        accumulated
    }

    pub fn free_vars(&self) -> Vec<&TyVar> {
        let mut vars = self.mono().free_vars();
        for pred in self.qualifiers.iter() {
            if let Predicate::Class(cl) = pred {
                for arg in cl.args.iter() {
                    vars.extend(arg.free_vars());
                }
            }
        }

        vars
    }

    pub fn free_ty_vars(&self, out: &mut HashSet<TyVar>) {
        self.mono().free_ty_vars(out);
        for pred in self.qualifiers.iter() {
            if let Predicate::Class(cl) = pred {
                for arg in cl.args.iter() {
                    arg.free_ty_vars(out);
                }
            }
        }
    }
}

/// Nominal structs, traits, and impls

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NominalKind {
    Struct,
}

impl std::fmt::Display for NominalKind {
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

impl std::fmt::Display for StructTy {
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

impl std::hash::Hash for StructTy {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.path.hash(state);
    }
}

impl StructTy {
    /// Look up a field by name on this struct, returning its index and type
    /// scheme if present.
    pub fn get_field(&self, name: &str) -> Option<(usize, &TyScheme)> {
        self.fields
            .iter()
            .enumerate()
            .find_map(|(idx, (field_name, ty))| {
                if field_name == name {
                    Some((idx, ty))
                } else {
                    None
                }
            })
    }

    /// Return the field types for this struct in declaration order.
    pub fn field_tys(&self) -> Vec<TyScheme> {
        self.fields.iter().map(|(_, ty)| ty.clone()).collect()
    }
}

impl Substitutable for StructTy {
    fn apply_subst(&mut self, subst: &Subst) {
        self.ty.apply_subst(subst);
        for (_, field_ty) in &mut self.fields {
            field_ty.apply_subst(subst);
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldKind {
    Method,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraitField {
    pub kind: FieldKind,
    pub name: String,
    pub ty: TyScheme,
    pub is_static: bool,
    pub recv_mode: ReceiverMode,
}

impl Substitutable for TraitField {
    fn apply_subst(&mut self, subst: &Subst) {
        self.ty.apply_subst(subst);
    }
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
    /// Optional default type for the receiver, corresponding to a
    /// `default(T)` marker in the trait definition (Section 8.2).
    pub default_ty: Option<Ty>,
}

impl Substitutable for TraitTy {
    fn apply_subst(&mut self, subst: &Subst) {
        self.ty.apply_subst(subst);
        for t in &mut self.super_traits {
            t.apply_subst(subst);
        }
        for f in &mut self.fields {
            f.apply_subst(subst);
        }
        if let Some(dt) = &mut self.default_ty {
            dt.apply_subst(subst);
        }
    }
}

impl TraitTy {
    pub fn get_field(&self, name: &str) -> Option<&TraitField> {
        self.fields.iter().find(|f| &f.name == name)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImplField {
    pub kind: FieldKind,
    pub path: Path,
    pub scheme: Option<TyScheme>,
    pub src: Source,
}

impl Substitutable for ImplField {
    fn apply_subst(&mut self, subst: &Subst) {
        if let Some(s) = &mut self.scheme {
            s.apply_subst(subst);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImplTy {
    pub base_ty: Ty,
    pub trait_ty: Ty,
    pub ty_args: Vec<Ty>,
    pub predicates: Vec<Predicate>,
    pub fields: Vec<ImplField>,
}

impl Substitutable for ImplTy {
    fn apply_subst(&mut self, subst: &Subst) {
        self.base_ty.apply_subst(subst);
        self.trait_ty.apply_subst(subst);
        for arg in &mut self.ty_args {
            arg.apply_subst(subst);
        }
        for pred in &mut self.predicates {
            pred.apply_subst(subst);
        }
        for f in &mut self.fields {
            f.apply_subst(subst);
        }
    }
}

impl ImplTy {
    pub fn free_ty_vars(&self, out: &mut HashSet<TyVar>) {
        self.base_ty.free_ty_vars(out);
        for arg in &self.ty_args {
            arg.free_ty_vars(out);
        }
        for pred in &self.predicates {
            pred.free_ty_vars(out);
        }
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

impl TraitTy {
    pub fn field_tys(&self) -> Vec<TyScheme> {
        todo!("TraitTy::field_tys is not yet implemented");
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

#[cfg(test)]
mod tests {
    use crate::types::Ty;

    #[test]
    fn func_eq() {
        let f1 = Ty::func(vec![Ty::var("?t0"), Ty::var("?t0")], Ty::var("?t1"));
        let f2 = Ty::func(vec![Ty::var("?t0"), Ty::var("?t0")], Ty::var("?t1"));
        assert_eq!(f1, f2)
    }
}

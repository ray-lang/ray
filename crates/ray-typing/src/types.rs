use std::collections::{HashMap, HashSet};
use std::ops::{Deref, DerefMut};

use ray_shared::{
    collections::{namecontext::NameContext, nametree::Scope},
    pathlib::Path,
    span::Source,
    ty::{Ty, TyVar},
};
use serde::{Deserialize, Serialize};

use crate::constraints::Predicate;
use crate::unify::mgu;

// Global substitution map for type variables.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
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

    pub fn merge_checked(&mut self, other: &Subst) -> bool {
        for (_, ty) in self.iter_mut() {
            ty.apply_subst(other);
        }

        for (var, ty) in other.iter() {
            if let Some(existing) = self.get(var) {
                let mut existing_ty = existing.clone();
                existing_ty.apply_subst(self);
                let mut next_ty = ty.clone();
                next_ty.apply_subst(self);
                if existing_ty != next_ty {
                    return false;
                }
            } else {
                self.insert(var.clone(), ty.clone());
            }
        }

        true
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

impl Substitutable for TyVar {
    fn apply_subst(&mut self, subst: &Subst) {
        if let Some(Ty::Var(var)) = subst.get(self) {
            *self = var.clone();
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
        self.vars.apply_subst(subst);
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
                write!(f, ",")?;
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
    pub is_static: bool,
    pub recv_mode: ReceiverMode,
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
pub enum ImplKind {
    Inherent {
        recv_ty: Ty,
    },
    Trait {
        base_ty: Ty,
        trait_ty: Ty,
        ty_args: Vec<Ty>,
    },
}

impl Substitutable for ImplKind {
    fn apply_subst(&mut self, subst: &Subst) {
        match self {
            ImplKind::Inherent { recv_ty } => recv_ty.apply_subst(subst),
            ImplKind::Trait {
                base_ty,
                trait_ty,
                ty_args,
            } => {
                base_ty.apply_subst(subst);
                trait_ty.apply_subst(subst);
                ty_args.apply_subst(subst);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImplTy {
    pub kind: ImplKind,
    pub predicates: Vec<Predicate>,
    pub fields: Vec<ImplField>,
}

impl Substitutable for ImplTy {
    fn apply_subst(&mut self, subst: &Subst) {
        self.kind.apply_subst(subst);
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
        match &self.kind {
            ImplKind::Inherent { recv_ty } => {
                recv_ty.free_ty_vars(out);
            }
            ImplKind::Trait {
                base_ty, ty_args, ..
            } => {
                base_ty.free_ty_vars(out);
                for arg in ty_args {
                    arg.free_ty_vars(out);
                }
            }
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
        let mut type_args = self.ty.type_arguments();
        if !type_args.is_empty() {
            if let Some(receiver_ty) = receiver_ty {
                if !type_args.is_empty() {
                    type_args[0] = receiver_ty;
                }
            }
            method_path = method_path.append_type_args(type_args.into_iter());
        }

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

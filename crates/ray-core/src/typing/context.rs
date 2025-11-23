use std::{
    cell::{RefCell, RefMut},
    collections::HashMap,
    fmt::Display,
    ops::DerefMut,
    rc::Rc,
};

use serde::{Deserialize, Serialize};
use top::{Predicates, Subst, Substitutable};

use crate::{
    ast::{FuncSig, Node, Path},
    collections::nametree::Scope,
    errors::RayError,
    pathlib::FilePath,
    sema::NameContext,
    span::SourceMap,
    typing::ty::TraitField,
};

use super::{
    state::TyVarFactory,
    ty::{ImplTy, StructTy, TraitTy, Ty, TyScheme, TyVar},
};

pub type InvertedVarMap = HashMap<TyVar, TyVar>;

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TyCtx {
    ty_map: HashMap<u64, Ty>,
    ty_scheme_map: HashMap<u64, TyScheme>,
    original_ty_map: HashMap<u64, Ty>,
    predicates: Predicates<Ty, TyVar>,
    scheme_subst: Subst<TyVar, TyScheme>,
    inst_ty_map: Subst<TyVar, TyScheme>,
    infix_ops: HashMap<String, (Path, Path)>,
    prefix_ops: HashMap<String, (Path, Path)>,
    var_map: HashMap<TyVar, TyVar>,
    struct_tys: HashMap<Path, StructTy>,
    traits: HashMap<Path, TraitTy>,
    impls: HashMap<Path, Vec<ImplTy>>,
    call_resolutions: HashMap<u64, Path>,
    tf: Rc<RefCell<TyVarFactory>>,
    inverted_var_map: Rc<RefCell<InvertedVarMap>>,
}

impl Clone for TyCtx {
    fn clone(&self) -> Self {
        Self {
            ty_map: self.ty_map.clone(),
            ty_scheme_map: self.ty_scheme_map.clone(),
            original_ty_map: self.original_ty_map.clone(),
            predicates: self.predicates.clone(),
            scheme_subst: self.scheme_subst.clone(),
            inst_ty_map: self.inst_ty_map.clone(),
            infix_ops: self.infix_ops.clone(),
            prefix_ops: self.prefix_ops.clone(),
            var_map: self.var_map.clone(),
            struct_tys: self.struct_tys.clone(),
            traits: self.traits.clone(),
            impls: self.impls.clone(),
            call_resolutions: self.call_resolutions.clone(),
            tf: Rc::clone(&self.tf),
            inverted_var_map: Rc::clone(&self.inverted_var_map),
        }
    }
}

impl Display for TyCtx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TyCtx {{")?;
        write!(f, "  ty_map: {{")?;
        for (k, v) in &self.ty_map {
            write!(f, "    {}: {},", k, v)?;
        }
        write!(f, "  }}")?;
        write!(f, "  ty_scheme_map: {{")?;
        for (k, v) in &self.ty_scheme_map {
            write!(f, "    {}: {},", k, v)?;
        }
        write!(f, "  }}")?;
        write!(f, "  original_ty_map: {{")?;
        for (k, v) in &self.original_ty_map {
            write!(f, "    {}: {},", k, v)?;
        }
        write!(f, "  }}")?;

        write!(f, "  predicates: [")?;
        for pred in self.predicates.iter() {
            write!(f, "    {},", pred)?;
        }
        write!(f, "  ]")?;

        write!(f, "  scheme_subst: {{")?;
        for (k, v) in self.scheme_subst.iter() {
            write!(f, "    {}: {},", k, v)?;
        }
        write!(f, "  }}")?;

        write!(f, "  inst_ty_map: {{")?;
        for (k, v) in self.inst_ty_map.iter() {
            write!(f, "    {}: {},", k, v)?;
        }
        write!(f, "  }}")?;
        write!(f, "  infix_ops: {{")?;
        for (k, (p1, p2)) in &self.infix_ops {
            write!(f, "    {}: ({}, {}),", k, p1, p2)?;
        }
        write!(f, "  }}")?;
        write!(f, "  prefix_ops: {{")?;
        for (k, (p1, p2)) in &self.prefix_ops {
            write!(f, "    {}: ({}, {}),", k, p1, p2)?;
        }
        write!(f, "  }}")?;
        write!(f, "  vars: {{")?;
        for (k, v) in &self.var_map {
            write!(f, "    {}: {},", k, v)?;
        }
        write!(f, "  }}")?;
        write!(f, "  struct_tys: {{")?;
        for (k, v) in &self.struct_tys {
            write!(f, "    {}: {:?},", k, v)?;
        }
        write!(f, "  }}")?;
        write!(f, "  traits: {{")?;
        for (k, v) in &self.traits {
            write!(f, "    {}: {:?},", k, v)?;
        }
        write!(f, "  }}")?;
        write!(f, "  impls: {{")?;
        for (k, v) in &self.impls {
            write!(f, "    {}: {:?},", k, v)?;
        }
        write!(f, "  }}")?;
        write!(f, "  call_resolutions: {{")?;
        for (k, v) in &self.call_resolutions {
            write!(f, "    {}: {},", k, v)?;
        }
        write!(f, "  }}")?;
        write!(f, "  tf: {:?},", self.tf)?;
        write!(f, "}}")
    }
}

impl Substitutable<TyVar, Ty> for TyCtx {
    fn apply_subst(&mut self, subst: &Subst<TyVar, Ty>) {
        for (id, ty) in self.ty_map.iter_mut() {
            if let Some(scheme) = self.ty_scheme_map.get(id) {
                if scheme.has_quantifiers() {
                    continue;
                }
            }
            ty.apply_subst(subst);
        }

        for scheme in self.ty_scheme_map.values_mut() {
            if scheme.has_quantifiers() {
                continue;
            }
            scheme.apply_subst(subst);
        }

        for (_, fqn) in self.call_resolutions.iter_mut() {
            fqn.apply_subst(subst);
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<TyVar, Ty>) {
        for (id, ty) in self.ty_map.iter_mut() {
            if let Some(scheme) = self.ty_scheme_map.get(id) {
                if scheme.has_quantifiers() {
                    continue;
                }
            }
            ty.apply_subst_all(subst);
        }

        for scheme in self.ty_scheme_map.values_mut() {
            if scheme.has_quantifiers() {
                continue;
            }
            scheme.apply_subst_all(subst);
        }
    }
}

// impl ApplySubst for TyCtx {
//     fn apply_subst(mut self, subst: &Subst) -> Self {
//         for ty in self.ty_map.values_mut() {
//             ty.apply_subst_mut(subst);
//         }
//         self
//     }
// }

// impl HasFreeVars for TyCtx {
//     fn free_vars(&self) -> HashSet<&TyVar> {
//         self.vars
//             .iter()
//             .filter_map(|(_, t)| if let Ty::Var(v) = t { Some(v) } else { None })
//             .collect()
//     }
// }

impl TyCtx {
    pub fn new() -> Self {
        Self {
            original_ty_map: HashMap::new(),
            ty_map: HashMap::new(),
            ty_scheme_map: HashMap::new(),
            predicates: Predicates::new(),
            scheme_subst: Subst::new(),
            inst_ty_map: Subst::new(),
            infix_ops: HashMap::new(),
            prefix_ops: HashMap::new(),
            var_map: HashMap::new(),
            struct_tys: HashMap::new(),
            traits: HashMap::new(),
            impls: HashMap::new(),
            call_resolutions: HashMap::new(),
            tf: Rc::new(RefCell::new(TyVarFactory::new("?t"))),
            inverted_var_map: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub fn extend(&mut self, other: TyCtx) {
        self.original_ty_map.extend(other.original_ty_map);
        self.ty_map.extend(other.ty_map);
        self.inst_ty_map.extend(other.inst_ty_map);
        self.infix_ops.extend(other.infix_ops);
        self.prefix_ops.extend(other.prefix_ops);
        self.struct_tys.extend(other.struct_tys);
        self.traits.extend(other.traits);
        self.impls.extend(other.impls);
        self.call_resolutions.extend(other.call_resolutions);
    }

    pub fn traits(&self) -> &HashMap<Path, TraitTy> {
        &self.traits
    }

    pub fn impls(&self) -> &HashMap<Path, Vec<ImplTy>> {
        &self.impls
    }

    pub fn structs(&self) -> &HashMap<Path, StructTy> {
        &self.struct_tys
    }

    pub fn extend_predicates(&mut self, predicates: Predicates<Ty, TyVar>) {
        self.predicates.extend(predicates);
    }

    pub fn extend_scheme_subst(&mut self, scheme_subst: Subst<TyVar, TyScheme>) {
        self.scheme_subst.extend(scheme_subst);
    }

    pub fn extend_inst_ty_map(&mut self, inst_ty_map: Subst<TyVar, TyScheme>) {
        self.inst_ty_map.extend(inst_ty_map);
    }

    pub fn ty_of(&self, id: u64) -> TyScheme {
        if let Some(scheme) = self.maybe_ty_scheme_of(id) {
            return scheme;
        }

        if let Some(ty) = self.get_ty(id) {
            if let Ty::Var(tv) = ty {
                if let Some(scheme) = self.scheme_subst.get(tv).cloned() {
                    return scheme;
                }
            }
            return ty.clone().into();
        }

        panic!("could not find type of id {:x}", id);
    }

    pub fn get_ty(&self, id: u64) -> Option<&Ty> {
        self.ty_map.get(&id)
    }

    pub fn original_ty_of(&self, id: u64) -> Option<&Ty> {
        self.original_ty_map.get(&id)
    }

    pub fn set_ty(&mut self, id: u64, ty: Ty) {
        self.original_ty_map.insert(id, ty.clone());
        self.ty_map.insert(id, ty);
    }

    pub fn ty_scheme_of(&self, id: u64) -> TyScheme {
        let mut scheme = self.ty_scheme_map.get(&id).unwrap().clone();
        scheme.generalize_in_place();
        scheme
    }

    pub fn maybe_ty_scheme_of(&self, id: u64) -> Option<TyScheme> {
        self.ty_scheme_map.get(&id).cloned().map(|mut scheme| {
            scheme.generalize_in_place();
            scheme
        })
    }

    pub fn set_ty_scheme(&mut self, id: u64, ty_scheme: TyScheme) {
        self.ty_scheme_map.insert(id, ty_scheme);
    }

    pub fn inst_ty_of(&self, tv: &TyVar) -> Option<&TyScheme> {
        self.inst_ty_map.get(tv)
    }

    pub fn into_ty_map(self) -> HashMap<u64, Ty> {
        self.ty_map
    }

    pub fn inst_ty_map(&self) -> &Subst<TyVar, TyScheme> {
        &self.inst_ty_map
    }

    pub fn get_poly_ty<T>(&self, node: &Node<T>) -> Option<&TyScheme> {
        let original = self.original_ty_of(node.id);
        match original {
            Some(Ty::Var(original_ty)) => {
                let inst_entry = self.inst_ty_of(original_ty);
                log::debug!(
                    "get_poly_ty: node={:#x} original_ty={} inst_hit={} inst_has_quantifiers={}",
                    node.id,
                    original_ty,
                    inst_entry.is_some(),
                    inst_entry
                        .map(|scheme| scheme.has_quantifiers())
                        .unwrap_or(false)
                );
                inst_entry.and_then(|scheme| {
                    if scheme.has_quantifiers() {
                        log::debug!(
                            "get_poly_ty: returning polymorphic scheme {} for {}",
                            scheme,
                            original_ty
                        );
                        Some(scheme)
                    } else {
                        log::debug!(
                            "get_poly_ty: inst scheme {} for {} is monomorphic; ignoring",
                            scheme,
                            original_ty
                        );
                        None
                    }
                })
            }
            other => {
                log::debug!(
                    "get_poly_ty: node={:#x} has no original Ty::Var entry (original={:?})",
                    node.id,
                    other
                );
                None
            }
        }
    }

    pub fn mk_tvar(&mut self, id: u64) -> Ty {
        let ty = Ty::Var(self.tf().next());
        self.set_ty(id, ty.clone());
        ty
    }

    pub fn resolve_trait_from_path(&self, path: &Path) -> Option<Path> {
        let parent_path = path.parent();
        if self.traits.contains_key(&parent_path) {
            Some(parent_path)
        } else {
            None
        }
    }

    pub fn lookup_infix_op(&self, name: &String) -> Option<&(Path, Path)> {
        self.infix_ops.get(name)
    }

    pub fn lookup_prefix_op(&self, name: &String) -> Option<&(Path, Path)> {
        self.prefix_ops.get(name)
    }

    pub fn add_infix_op(&mut self, name: String, infix_op: Path, trait_fqn: Path) {
        self.infix_ops.insert(name, (infix_op, trait_fqn));
    }

    pub fn add_prefix_op(&mut self, name: String, prefix_op: Path, trait_fqn: Path) {
        self.prefix_ops.insert(name, (prefix_op, trait_fqn));
    }

    pub fn add_var_mapping(&mut self, lhs: TyVar, rhs: TyVar) {
        log::debug!("add var mapping: {} -> {}", lhs, rhs);
        self.var_map.insert(lhs.clone(), rhs.clone());
        self.inverted_var_map.borrow_mut().entry(rhs).or_insert(lhs);
    }

    pub fn get_var_mapping(&self, var: &TyVar) -> Option<&TyVar> {
        self.var_map.get(var)
    }

    pub fn inverted_var_map(&self) -> &Rc<RefCell<InvertedVarMap>> {
        &self.inverted_var_map
    }

    /// Produce a "pretty" version of a type for display (e.g., in diagnostics
    /// or IDE hovers) by rewriting internal solver type variables back to the
    /// original user-declared type variables, using `inverted_var_map`.
    pub fn pretty_ty(&self, ty: &Ty) -> Ty {
        let mut result = ty.clone();

        // Build a substitution that maps each solver TyVar back to its original
        // user TyVar (e.g., ?t1431 -> 'a), then apply it to the type.
        let rename_subst: Subst<TyVar, Ty> = self
            .inverted_var_map
            .borrow()
            .iter()
            .map(|(solver, original)| (solver.clone(), Ty::Var(original.clone())))
            .collect();

        result.apply_subst(&rename_subst);
        result
    }

    pub fn resolve_signature(
        &mut self,
        sig: &mut FuncSig,
        fn_scope: &Path,
        scopes: &Vec<Scope>,
        filepath: &FilePath,
        srcmap: &SourceMap,
        ncx: &NameContext,
    ) -> Result<(), RayError> {
        log::debug!("[resolve_signature] {}", sig);

        // first, resolve all FQNs in the signature: type params, params, return type, qualifiers
        if let Some(ty_params) = sig.ty_params.as_mut() {
            for ty_param in ty_params.tys.iter_mut() {
                ty_param.resolve_fqns(scopes, ncx);
            }
        }

        for param in sig.params.iter_mut() {
            if let Some(ty) = param.ty_mut() {
                ty.resolve_fqns(scopes, ncx);
            }
        }

        if let Some(ret_ty) = sig.ret_ty.as_mut() {
            ret_ty.resolve_fqns(scopes, ncx);
        }

        for qual in sig.qualifiers.iter_mut() {
            qual.resolve_fqns(scopes, ncx);
        }

        // then create a "fresh" scheme, replacing each schema variable with a meta variable
        let ty = TyScheme::from_sig(sig, fn_scope, filepath, self, srcmap)?;
        if let Some(ty_params) = &mut sig.ty_params {
            for ty_param in ty_params.tys.iter_mut() {
                let ty = ty_param.deref_mut();
                ty.map_vars(self);
            }
        }

        sig.ty = Some(ty);
        Ok(())
    }

    pub fn get_struct_ty(&self, fqn: &Path) -> Option<&StructTy> {
        self.struct_tys.get(fqn)
    }

    pub fn add_struct_ty(&mut self, struct_ty: StructTy) {
        self.struct_tys.insert(struct_ty.path.clone(), struct_ty);
    }

    pub fn set_call_resolution(&mut self, id: u64, path: Path) {
        self.call_resolutions.insert(id, path);
    }

    pub fn call_resolution(&self, id: u64) -> Option<Path> {
        self.call_resolutions.get(&id).cloned()
    }

    pub fn call_resolutions(&self) -> &HashMap<u64, Path> {
        &self.call_resolutions
    }

    pub fn get_trait_ty(&self, path: &Path) -> Option<&TraitTy> {
        // let fqn = self.nametree().find_in_scope(scope, name);
        self.traits.get(path)
    }

    pub fn get_super_traits_from_ty(&self, ty: &Ty) -> Option<&Vec<Ty>> {
        let fqn = ty.get_path();
        match self.get_trait_ty(&fqn) {
            Some(trait_ty) => Some(&trait_ty.super_traits),
            _ => None,
        }
    }

    pub fn get_trait_field(&self, trait_fqn: &Path, field_name: &str) -> Option<&TraitField> {
        self.get_trait_ty(trait_fqn).and_then(|trait_ty| {
            trait_ty.fields.iter().find_map(|field| {
                if &field.name == field_name {
                    Some(field)
                } else {
                    None
                }
            })
        })
    }

    pub fn get_trait_fn(&self, trait_fqn: &Path, fn_name: &String) -> Option<&TyScheme> {
        self.get_trait_ty(trait_fqn).and_then(|trait_ty| {
            trait_ty.fields.iter().find_map(|field| {
                if &field.name == fn_name {
                    Some(&field.ty)
                } else {
                    None
                }
            })
        })
    }

    pub fn add_trait_ty(&mut self, trait_ty: TraitTy) {
        self.traits.insert(trait_ty.path.clone(), trait_ty);
    }

    pub fn add_impl(&mut self, trait_fqn: Path, impl_ty: ImplTy) {
        if !self.impls.contains_key(&trait_fqn) {
            self.impls.insert(trait_fqn, vec![impl_ty]);
        } else {
            self.impls.get_mut(&trait_fqn).unwrap().push(impl_ty);
        }
    }

    pub fn get_impls(&self, ty: &Ty) -> Option<&Vec<ImplTy>> {
        let fqn = ty.get_path();
        self.impls.get(&fqn)
    }

    pub fn has_member(&self, fqn: &Path, member: &String) -> bool {
        if let Some(struct_ty) = self.get_struct_ty(&fqn) {
            struct_ty.fields.iter().any(|(f, _)| f == member)
        } else if let Some(trait_ty) = self.get_trait_ty(&fqn) {
            trait_ty.fields.iter().any(|field| &field.name == member)
        } else {
            false
        }
    }

    pub fn tf(&mut self) -> RefMut<'_, TyVarFactory> {
        self.tf.borrow_mut()
    }

    pub fn resolve_trait_method(&self, method_name: &str) -> Option<(&TraitTy, &TraitField)> {
        log::debug!("[resolve_trait_method] method={}", method_name);
        self.traits.iter().find_map(|(_, trait_ty)| {
            trait_ty
                .fields
                .iter()
                .find(|field| field.name == method_name)
                .map(|field| (trait_ty, field))
        })
    }
}

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use ray_shared::pathlib::ItemPath;
use ray_shared::resolution::DefTarget;
use ray_shared::{
    node_id::NodeId,
    pathlib::Path,
    ty::{SchemaVarAllocator, Ty, TyVar},
};
use serde::{Deserialize, Serialize};

use crate::{
    constraints::Predicate,
    env::GlobalEnv,
    types::{
        ImplField, ImplTy, NominalKind, StructTy, Subst, Substitutable, TraitField, TraitTy,
        TyScheme,
    },
};

/// Resolved call target information.
///
/// For trait methods, `trait_target` is set to the trait method's DefTarget,
/// and `impl_target` is set to the specific impl method if it's known at
/// type-check time (i.e., for monomorphic receiver types). For polymorphic
/// receivers, `impl_target` is `None` and dispatch happens at instantiation.
///
/// For inherent methods, `trait_target` is `None` and `impl_target` is set
/// to the method's DefTarget.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CallResolution {
    /// The trait method target, if this call is a trait method.
    pub trait_target: Option<DefTarget>,
    /// The impl/inherent method target, if known.
    pub impl_target: Option<DefTarget>,
    pub poly_callee_ty: TyScheme,
    pub callee_ty: TyScheme,
    pub subst: Subst,
}

impl CallResolution {
    /// Returns the most specific target available.
    ///
    /// Prefers `impl_target` (for codegen when the impl is known), falling back
    /// to `trait_target` (for polymorphic dispatch).
    pub fn target(&self) -> Option<&DefTarget> {
        self.impl_target.as_ref().or(self.trait_target.as_ref())
    }
}

/// High-level type context facade for the new type system.
///
/// This is intentionally shaped to be a drop-in replacement for the
/// parts of the original `ray_typing::TyCtx` that are used outside the
/// solver (e.g. in libgen, driver, and IDE tooling). Internally it is
/// backed by the new type system's `GlobalEnv` and a map of generalized
/// schemes for bindings.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct TyCtx {
    /// Global nominal environment: traits, structs, impls, and operator
    /// tables. This corresponds to the environment built during module
    /// combination and serialized into `.raylib` files.
    pub global_env: GlobalEnv,

    /// Final generalized schemes for each binding, keyed by fully
    /// qualified path. On the frontend side these are typically
    /// populated from the solver results.
    pub schemes: HashMap<Path, TyScheme>,

    /// Non-exported schemes keyed by fully qualified path.
    ///
    /// This is intended for debug/test tooling that wants access to schemes
    /// for locals without polluting the exported scheme map used for library
    /// linking.
    #[serde(default, skip)]
    pub all_schemes: HashMap<Path, TyScheme>,

    /// Node-id indexed mono types for the current module. This is the
    /// v2 analogue of the original TyCtx's `ty_map` and is populated
    /// from the solver's TypeContext using the frontend's ExprId/NodeId
    /// mapping.
    pub node_tys: HashMap<NodeId, Ty>,

    /// Node-id indexed schemes (where polymorphic). This mirrors the
    /// original TyCtx's `ty_scheme_map`.
    pub node_schemes: HashMap<NodeId, TyScheme>,

    /// Resolved call targets keyed by callee expression id.
    ///
    /// This is populated by a post-typecheck call-resolution pass and is
    /// intended for use by LIR/IDE consumers.
    #[serde(default, skip)]
    pub call_resolutions: HashMap<NodeId, CallResolution>,

    var_map: HashMap<TyVar, TyVar>,
    inverted_var_map: Rc<RefCell<HashMap<TyVar, TyVar>>>,
    schema_allocator: Rc<RefCell<SchemaVarAllocator>>,
}

impl Substitutable for TyCtx {
    fn apply_subst(&mut self, subst: &Subst) {
        self.global_env.apply_subst(subst);

        for (_, scheme) in self.schemes.iter_mut() {
            scheme.apply_subst(subst);
        }

        for (_, scheme) in self.all_schemes.iter_mut() {
            scheme.apply_subst(subst);
        }

        for (_, ty) in self.node_tys.iter_mut() {
            ty.apply_subst(subst);
        }

        for (_, scheme) in self.node_schemes.iter_mut() {
            scheme.apply_subst(subst);
        }
    }
}

impl TyCtx {
    pub fn new(global_env: GlobalEnv) -> Self {
        let allocator = Rc::new(RefCell::new(SchemaVarAllocator::new()));
        TyCtx::with_allocator(global_env, allocator)
    }

    pub fn with_allocator(
        global_env: GlobalEnv,
        schema_allocator: Rc<RefCell<SchemaVarAllocator>>,
    ) -> Self {
        TyCtx {
            global_env,
            schemes: HashMap::new(),
            all_schemes: HashMap::new(),
            node_tys: HashMap::new(),
            node_schemes: HashMap::new(),
            call_resolutions: HashMap::new(),
            var_map: HashMap::new(),
            inverted_var_map: Rc::new(RefCell::new(HashMap::new())),
            schema_allocator,
        }
    }

    /// Merge another context into this one. Existing entries in `self`
    /// are preserved; new ones from `other` are added.
    pub fn extend(&mut self, other: TyCtx) {
        self.global_env.extend(other.global_env);
        self.schemes.extend(other.schemes);
        self.all_schemes.extend(other.all_schemes);
        self.node_tys.extend(other.node_tys);
        self.node_schemes.extend(other.node_schemes);
        self.call_resolutions.extend(other.call_resolutions);
    }

    pub fn traits(&self) -> &HashMap<Path, TraitTy> {
        todo!("TyCtx::traits is not yet implemented for the v2 type system");
    }

    /// Access the underlying global environment.
    pub fn global_env(&self) -> &GlobalEnv {
        &self.global_env
    }

    /// Immutable view of all known schemes.
    pub fn schemes(&self) -> &HashMap<Path, TyScheme> {
        &self.schemes
    }

    /// Immutable view of all schemes, including non-exported locals.
    pub fn all_schemes(&self) -> &HashMap<Path, TyScheme> {
        &self.all_schemes
    }

    /// Mutable view of the schemes map, for callers that want to seed
    /// or update schemes for particular bindings.
    pub fn schemes_mut(&mut self) -> &mut HashMap<Path, TyScheme> {
        &mut self.schemes
    }

    /// Look up the scheme for a binding by its fully qualified path.
    pub fn scheme_of(&self, path: &Path) -> Option<&TyScheme> {
        self.schemes.get(path)
    }

    /// Look up the mono type for a node id.
    pub fn get_ty(&self, id: NodeId) -> Option<&Ty> {
        self.node_tys.get(&id)
    }

    /// Look up the scheme attached to a node id.
    pub fn maybe_ty_scheme_of(&self, id: NodeId) -> Option<TyScheme> {
        self.node_schemes.get(&id).cloned()
    }

    pub fn pretty_type_info_for_node(&self, node_id: NodeId) -> Option<(String, bool)> {
        if let Some(scheme) = self.maybe_ty_scheme_of(node_id) {
            Some((self.pretty_tys(&scheme).to_string(), true))
        } else if let Some(ty) = self.get_ty(node_id) {
            Some((self.pretty_tys(ty).to_string(), false))
        } else {
            None
        }
    }

    pub fn map_vars(&mut self, ty: &mut Ty) {
        match ty {
            Ty::Never | Ty::Any | Ty::Const(_) => {}
            Ty::Var(tv) => {
                if tv.is_ret_placeholder() {
                    return;
                }

                *tv = if let Some(mapped_tv) = self.get_var_mapping(tv) {
                    log::debug!("found mapping: {} -> {}", tv, mapped_tv);
                    mapped_tv.clone()
                } else {
                    let mapped_tv = self.new_schema_var();
                    self.add_var_mapping(tv.clone(), mapped_tv.clone());
                    mapped_tv
                };
            }
            Ty::Tuple(tys) => {
                tys.iter_mut().for_each(|t| self.map_vars(t));
            }
            Ty::Proj(_, param_tys) => {
                param_tys.iter_mut().for_each(|t| self.map_vars(t));
            }
            Ty::Array(inner, _) | Ty::Ref(inner) | Ty::RawPtr(inner) => self.map_vars(inner),
            Ty::Func(param_tys, ret_ty) => {
                param_tys.iter_mut().for_each(|t| self.map_vars(t));
                self.map_vars(ret_ty);
            }
        }
    }

    pub fn nominal_kind(&self, ty: &Ty) -> Option<NominalKind> {
        let fqn = ty.item_path()?;
        self.get_struct_ty(fqn).map(|s| s.kind)
    }

    pub fn is_struct(&self, ty: &Ty) -> bool {
        self.nominal_kind(ty) == Some(NominalKind::Struct)
    }

    /// Access the resolved call targets for this module.
    pub fn call_resolutions(&self) -> &HashMap<NodeId, CallResolution> {
        &self.call_resolutions
    }

    /// Produce a "pretty" version of a type for display by applying any
    /// internal solver renamings. For now this is a no-op that simply
    /// clones the input; once we track an inverted var map in the v2
    /// context we can mirror the original TyCtx behavior.
    pub fn pretty_tys<T>(&self, ty: &T) -> T
    where
        T: Clone + Substitutable,
    {
        let subst = self.inverted_var_subst();
        let mut out = ty.clone();
        out.apply_subst(&subst);
        out
    }

    pub fn extend_predicates(&mut self, _predicates: Vec<Predicate>) {
        todo!("extend_predicates is not yet implemented for v2 TyCtx");
    }

    pub fn extend_scheme_subst(&mut self, _scheme_subst: Subst) {
        todo!("extend_scheme_subst is not yet implemented for v2 TyCtx");
    }

    pub fn extend_inst_ty_map(&mut self, _inst_ty_map: Subst) {
        todo!("extend_inst_ty_map is not yet implemented for v2 TyCtx");
    }

    pub fn ty_of(&self, id: NodeId) -> TyScheme {
        if let Some(scheme) = self.maybe_ty_scheme_of(id) {
            return scheme;
        }
        if let Some(ty) = self.get_ty(id) {
            return TyScheme::from_mono(ty.clone());
        }
        panic!("could not find type of node {id}");
    }

    pub fn original_ty_of(&self, id: NodeId) -> Option<&Ty> {
        self.node_tys.get(&id)
    }

    pub fn set_ty(&mut self, id: NodeId, ty: Ty) {
        self.node_tys.insert(id, ty);
    }

    pub fn set_ty_scheme(&mut self, id: NodeId, ty_scheme: TyScheme) {
        self.node_schemes.insert(id, ty_scheme);
    }

    pub fn inst_ty_of(&self, _tv: &TyVar) -> Option<&TyScheme> {
        todo!("inst_ty_of is not yet implemented for v2 TyCtx");
    }

    pub fn into_ty_map(self) -> HashMap<NodeId, Ty> {
        self.node_tys
    }

    pub fn inst_ty_map(&self) -> &HashMap<TyVar, TyScheme> {
        todo!("inst_ty_map is not yet implemented for v2 TyCtx");
    }

    pub fn get_poly_ty(&self, node_id: NodeId) -> Option<&TyScheme> {
        self.node_schemes.get(&node_id)
    }

    pub fn is_scheme_var(&self, _var: &TyVar) -> bool {
        todo!("is_scheme_var is not yet implemented for v2 TyCtx");
    }

    pub fn resolve_trait_from_path(&self, _path: &ItemPath) -> Option<ItemPath> {
        unreachable!("DO NOT REMOVE THIS PANIC: legacy code should not be called")

        // let parent = path.parent();
        // let key = parent.to_string();
        // if self.global_env.traits.contains_key(&key) {
        //     Some(ItemPath::from(&parent))
        // } else {
        //     None
        // }
    }

    pub fn lookup_infix_op(&self, name: &String) -> Option<&(Path, Path)> {
        self.global_env.infix_ops.get(name)
    }

    pub fn lookup_prefix_op(&self, name: &String) -> Option<&(Path, Path)> {
        self.global_env.prefix_ops.get(name)
    }

    pub fn add_infix_op(&mut self, name: String, infix_op: Path, trait_fqn: Path) {
        self.global_env.register_infix_op(name, infix_op, trait_fqn);
    }

    pub fn add_prefix_op(&mut self, name: String, prefix_op: Path, trait_fqn: Path) {
        self.global_env
            .register_prefix_op(name, prefix_op, trait_fqn);
    }

    pub fn add_var_mapping(&mut self, lhs: TyVar, rhs: TyVar) {
        log::debug!("add var mapping: {} -> {}", lhs, rhs);
        self.var_map.insert(lhs.clone(), rhs.clone());
        self.inverted_var_map.borrow_mut().entry(rhs).or_insert(lhs);
    }

    pub fn get_var_mapping(&self, var: &TyVar) -> Option<&TyVar> {
        self.var_map.get(var)
    }

    pub fn schema_allocator(&self) -> Rc<RefCell<SchemaVarAllocator>> {
        self.schema_allocator.clone()
    }

    pub fn new_schema_var(&self) -> TyVar {
        self.schema_allocator.borrow_mut().alloc()
    }

    pub fn inverted_var_subst(&self) -> Subst {
        let mut subst = Subst::new();
        for (schema_var, original_var) in self.inverted_var_map.borrow().iter() {
            subst.insert(schema_var.clone(), Ty::Var(original_var.clone()));
        }
        subst
    }

    pub fn get_struct_ty(&self, fqn: &ItemPath) -> Option<&StructTy> {
        let key = fqn.to_string();
        self.global_env.structs.get(&key)
    }

    pub fn add_struct_ty(&mut self, struct_ty: StructTy) {
        let key = struct_ty.path.to_string();
        self.global_env.structs.insert(key, struct_ty);
    }

    pub fn set_call_resolution(&mut self, id: NodeId, resolution: CallResolution) {
        self.call_resolutions.insert(id, resolution);
    }

    pub fn call_resolution(&self, id: NodeId) -> Option<&CallResolution> {
        self.call_resolutions.get(&id)
    }

    /// Given a (possibly partially-instantiated) method FQN and the ids of the
    /// callee and arguments at a call site, compute a "normalized" impl FQN by
    /// mirroring the resolution logic used in LIR generation for method calls.
    ///
    /// This helper intentionally does *not* perform any of the LIR-specific
    /// name rewriting (such as `sema::fn_name` or extern remapping). It stops
    /// at the point where `Call::lir_gen` has constructed the fully
    /// instantiated base method path like:
    ///
    ///   scratch::Index::[scratch::A,scratch::B,uint]::get
    ///
    /// That is the form most useful for symbol/IDE indexing.
    pub fn resolve_method_impl_fqn(
        &self,
        _func_fqn: ItemPath,
        _call_resolution_id: NodeId,
        _callee_id: NodeId,
        _arg_ids: &[NodeId],
    ) -> ItemPath {
        unreachable!("DO NOT REMOVE THIS PANIC: legacy code should not be called")

        // // If constraint solving recorded a more precise method FQN for this
        // // call site (e.g., from trait resolution), prefer that.
        // if let Some(resolved) = self.call_resolution(call_resolution_id) {
        //     log::debug!(
        //         "[TyCtx::resolve_method_impl_fqn] resolved call: {} -> {}",
        //         func_fqn,
        //         resolved.base_fqn
        //     );
        //     func_fqn = resolved.base_fqn.clone();
        // }

        // log::debug!(
        //     "[TyCtx::resolve_method_impl_fqn] initial func_fqn = {}",
        //     func_fqn
        // );

        // // Reconstruct the substitution that `Call::lir_gen` derives from the
        // // callee and argument types by re-running the same type-level logic
        // // here in the type context, using only ids and `TyCtx` queries.
        // //
        // // This intentionally mirrors:
        // //
        // //   let callee_scheme = tcx.ty_of(call.callee.id);
        // //   let mut fn_ty = tcx.instantiate_scheme(callee_scheme.clone());
        // //   ...
        // //   let subst = fn_ty.instantiate_fn_with_args(instantiated_poly_ty.as_mut(), &mut arg_tys);
        // //
        // let callee_scheme = self.ty_of(callee_id);
        // let mut fn_ty = self.instantiate_scheme(callee_scheme.clone());

        // let mut arg_tys: Vec<TyScheme> = arg_ids.iter().map(|id| self.ty_of(*id)).collect();

        // let original_poly_ty = self.get_poly_ty(callee_id).cloned();
        // let mut instantiated_poly_ty = original_poly_ty
        //     .clone()
        //     .map(|ty| self.instantiate_scheme(ty));

        // let subst = fn_ty.instantiate_fn_with_args(instantiated_poly_ty.as_mut(), &mut arg_tys);
        // log::debug!(
        //     "[TyCtx::resolve_method_impl_fqn] subst from args = {}",
        //     subst
        // );

        // if !subst.is_empty() {
        //     func_fqn.apply_subst(&subst);
        //     log::debug!(
        //         "[TyCtx::resolve_method_impl_fqn] after arg subst: {}",
        //         func_fqn
        //     );
        // }

        // // Next, mirror the trait-based refinement used in `Call::lir_gen`:
        // //  - Normalize to a trait path.
        // //  - Find the corresponding trait field.
        // //  - If we have an instantiated polymorphic type for the call, unify
        // //    it with the trait field's type to refine the substitution and
        // //    apply that to the method FQN.
        // let norm_func_fqn = func_fqn.with_names_only();
        // let trait_fqn = self.resolve_trait_from_path(&norm_func_fqn);
        // let field = trait_fqn
        //     .as_ref()
        //     .and_then(|trait_fqn| self.get_trait_field(trait_fqn, &func_fqn.name().unwrap()));

        // log::debug!(
        //     "[TyCtx::resolve_method_impl_fqn] trait_fqn={:?} field={:?}",
        //     trait_fqn,
        //     field.as_ref().map(|f| &f.name)
        // );

        // if let (Some(inst_ty), Some(field)) = (instantiated_poly_ty.as_ref(), field) {
        //     let trait_fn_ty = &field.ty;
        //     log::debug!(
        //         "[TyCtx::resolve_method_impl_fqn] inst_ty: {}, trait_fn_ty: {}",
        //         inst_ty,
        //         trait_fn_ty
        //     );

        //     if let Ok((_, trait_subst)) = mgu(trait_fn_ty.mono(), inst_ty.mono()) {
        //         log::debug!(
        //             "[TyCtx::resolve_method_impl_fqn] trait_subst: {}",
        //             trait_subst
        //         );
        //         func_fqn.apply_subst(&trait_subst);
        //         log::debug!(
        //             "[TyCtx::resolve_method_impl_fqn] after trait subst: {}",
        //             func_fqn
        //         );
        //     }
        // }

        // func_fqn
    }

    pub fn get_trait_ty(&self, path: &ItemPath) -> Option<&TraitTy> {
        let key = path.to_string();
        self.global_env.traits.get(&key)
    }

    pub fn get_super_traits_from_ty(&self, ty: &Ty) -> Option<&Vec<Ty>> {
        let fqn = ty.item_path()?;
        self.get_trait_ty(fqn)
            .map(|trait_ty| &trait_ty.super_traits)
    }

    pub fn get_trait_field(&self, trait_fqn: &ItemPath, field_name: &str) -> Option<&TraitField> {
        self.get_trait_ty(trait_fqn).and_then(|trait_ty| {
            trait_ty
                .fields
                .iter()
                .find(|field| field.name == field_name)
        })
    }

    pub fn get_trait_fn(&self, trait_fqn: &ItemPath, fn_name: &String) -> Option<&TyScheme> {
        self.get_trait_ty(trait_fqn).and_then(|trait_ty| {
            trait_ty
                .fields
                .iter()
                .find(|field| &field.name == fn_name)
                .map(|field| &field.ty)
        })
    }

    pub fn add_trait_ty(&mut self, trait_ty: TraitTy) {
        let key = trait_ty.path.to_string();
        self.global_env.traits.insert(key, trait_ty);
    }

    pub fn add_impl(&mut self, _trait_fqn: Path, impl_ty: ImplTy) {
        self.global_env.add_impl(impl_ty);
    }

    pub fn get_impls_for_trait_fqn(&self, _fqn: &ItemPath) -> Vec<&ImplTy> {
        unreachable!("legacy code should no longer be called")

        // let target = fqn.to_string();
        // self.global_env
        //     .impls_by_trait
        //     .get(&target)
        //     .into_iter()
        //     .flatten()
        //     .flat_map(|idx| self.global_env.resolve_impl_from_index(idx))
    }

    pub fn has_member(&self, fqn: &ItemPath, member: &String) -> bool {
        if let Some(struct_ty) = self.get_struct_ty(fqn) {
            struct_ty.fields.iter().any(|(f, _)| f == member)
        } else if let Some(trait_ty) = self.get_trait_ty(fqn) {
            trait_ty.fields.iter().any(|field| &field.name == member)
        } else {
            false
        }
    }

    pub fn resolve_trait_method(&self, method_name: &str) -> Option<(&TraitTy, &TraitField)> {
        self.global_env.traits.iter().find_map(|(_, trait_ty)| {
            trait_ty
                .fields
                .iter()
                .find(|field| field.name == method_name)
                .map(|field| (trait_ty, field))
        })
    }

    pub fn resolve_inherent_method(
        &self,
        recv_fqn: &ItemPath,
        method_name: &str,
    ) -> Option<(&ImplTy, &ImplField)> {
        let recv_key = recv_fqn.to_string();
        self.global_env
            .inherent_impls_for_key(&recv_key)
            .find_map(|impl_ty| {
                match impl_ty.fields.iter().find(|f| match f.path.item_name() {
                    Some(name) if name == method_name => true,
                    _ => false,
                }) {
                    Some(field) => Some((impl_ty, field)),
                    _ => None,
                }
            })
    }

    pub fn instantiate_scheme(&self, scheme: TyScheme) -> TyScheme {
        scheme
    }
}

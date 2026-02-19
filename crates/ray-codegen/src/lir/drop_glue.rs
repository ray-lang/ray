use std::collections::{BTreeMap, HashMap};

use ray_lir as lir;
use ray_shared::{
    pathlib::{ItemPath, Path},
    ty::Ty,
};
use ray_typing::types::{ImplKind, ImplTy, StructTy, TyScheme};

/// Generate drop glue functions and patch `DecRef` instructions.
///
/// For each struct type that has reference-typed fields or a `Destruct` impl,
/// generates a `__drop_<T>` function that:
///   1. Calls the user's `destruct` method (if `Destruct` is implemented)
///   2. Decrements refcounts for each reference-typed field in declaration order
///
/// Then patches all `DecRef(val, Strong, None)` instructions whose pointee
/// type has a drop function to `DecRef(val, Strong, Some(drop_fn_ref))`.
pub fn generate_drop_glue(program: &mut lir::Program) {
    let struct_types = program.struct_types.clone();
    let impls_by_trait = program.impls_by_trait.clone();

    // Phase 1: Determine which struct types need drop glue and build drop functions.
    let mut drop_fn_map: HashMap<ItemPath, DropFnInfo> = HashMap::new();

    for (struct_path, struct_ty) in &struct_types {
        let destruct_info = find_destruct_impl(struct_path, struct_ty, &impls_by_trait);
        let needs_field_drops = has_ref_fields(struct_ty, &struct_types);

        if destruct_info.is_none() && !needs_field_drops {
            continue;
        }

        let info = build_drop_fn(
            struct_path,
            struct_ty,
            destruct_info,
            &struct_types,
            &drop_fn_map,
        );
        drop_fn_map.insert(struct_path.clone(), info);
    }

    // Phase 2: Add drop functions to the program.
    for info in drop_fn_map.values() {
        program.funcs.push(info.func.clone());
    }

    // Phase 3: Patch existing DecRef instructions in all functions.
    patch_decref_instructions(program, &drop_fn_map);
}

/// Information about a generated drop function.
struct DropFnInfo {
    func: lir::Func,
    /// The drop function's name (used to create FuncRef in DecRef instructions).
    name: Path,
    /// The drop function's type scheme (monomorphic or polymorphic).
    ty: TyScheme,
    /// The polymorphic type scheme (if the struct is generic), used by the
    /// monomorphizer to know this is a polymorphic reference.
    poly_ty: Option<TyScheme>,
}

/// Information about a Destruct impl for a struct type.
struct DestructInfo {
    /// Path to the destruct method's LIR function (e.g., `test::Destruct::destruct`).
    method_path: Path,
    /// The destruct method's type scheme.
    method_ty: TyScheme,
    /// The polymorphic type scheme for the destruct method (if generic).
    method_poly_ty: Option<TyScheme>,
}

/// Check if a struct type has any reference-typed fields (directly or
/// transitively through value-type struct fields).
fn has_ref_fields(struct_ty: &StructTy, all_structs: &HashMap<ItemPath, StructTy>) -> bool {
    for (_name, field_ty) in &struct_ty.fields {
        let mono = field_ty.mono();
        match mono {
            Ty::Ref(_) | Ty::MutRef(_) | Ty::IdRef(_) => return true,
            Ty::Proj(path, _) | Ty::Const(path) => {
                if let Some(nested) = all_structs.get(path) {
                    if has_ref_fields(nested, all_structs) {
                        return true;
                    }
                }
            }
            _ => {}
        }
    }
    false
}

/// Look up a Destruct impl for the given struct type.
fn find_destruct_impl(
    struct_path: &ItemPath,
    struct_ty: &StructTy,
    impls_by_trait: &BTreeMap<ItemPath, Vec<ImplTy>>,
) -> Option<DestructInfo> {
    for (trait_path, impls) in impls_by_trait {
        if trait_path.item_name() != Some("Destruct") {
            continue;
        }

        for impl_ty in impls {
            let ImplKind::Trait { base_ty, .. } = &impl_ty.kind else {
                continue;
            };

            // Check if the impl's base type matches our struct path.
            let impl_path = match base_ty {
                Ty::Const(p) | Ty::Proj(p, _) => p,
                _ => continue,
            };

            if impl_path != struct_path {
                continue;
            }

            // Found a matching Destruct impl. Get the destruct method.
            let destruct_field = impl_ty
                .fields
                .iter()
                .find(|f| f.path.item_name() == Some("destruct"))?;

            let method_path = destruct_field.path.to_path();
            let method_ty = destruct_field.scheme.clone().unwrap_or_else(|| {
                // If no scheme, build one from the struct type.
                let param_ty = Ty::mut_ref_of(struct_ty.ty.mono().clone());
                TyScheme::from_mono(Ty::Func(vec![param_ty], Box::new(Ty::unit())))
            });

            let method_poly_ty = if struct_ty.ty.is_polymorphic() {
                Some(method_ty.clone())
            } else {
                None
            };

            return Some(DestructInfo {
                method_path,
                method_ty,
                method_poly_ty,
            });
        }
    }
    None
}

/// Build a drop glue function for a struct type.
fn build_drop_fn(
    struct_path: &ItemPath,
    struct_ty: &StructTy,
    destruct_info: Option<DestructInfo>,
    all_structs: &HashMap<ItemPath, StructTy>,
    drop_fn_map: &HashMap<ItemPath, DropFnInfo>,
) -> DropFnInfo {
    // Name: __drop::<struct_path>
    let drop_fn_name = Path::from(format!("__drop::{}", struct_path));

    // Type: fn(*mut T) -> ()
    let struct_mono_ty = struct_ty.ty.mono().clone();
    let self_param_ty = Ty::mut_ref_of(struct_mono_ty);
    let fn_ty_mono = Ty::Func(vec![self_param_ty.clone()], Box::new(Ty::unit()));

    let fn_ty = if struct_ty.ty.is_polymorphic() {
        TyScheme {
            vars: struct_ty.ty.quantifiers().clone(),
            qualifiers: vec![],
            ty: fn_ty_mono,
        }
    } else {
        TyScheme::from_mono(fn_ty_mono)
    };

    let poly_ty = if fn_ty.is_polymorphic() {
        Some(fn_ty.clone())
    } else {
        None
    };

    // Build function body.
    let mut symbols = lir::SymbolSet::new();
    let mut block = lir::Block::new(0);
    let mut locals: Vec<lir::Local> = vec![];

    // Parameter 0: self of type *mut T
    let self_local_idx = 0;
    locals.push(lir::Local {
        idx: self_local_idx,
        ty: TyScheme::from_mono(self_param_ty.clone()),
    });
    let params = vec![lir::Param::new(
        "self".to_string(),
        self_local_idx,
        self_param_ty,
    )];

    // 1. Call destruct if the struct implements Destruct.
    if let Some(info) = &destruct_info {
        symbols.insert(info.method_path.clone());
        let call = lir::Call::new(
            info.method_path.clone(),
            vec![lir::Variable::Local(self_local_idx)],
            info.method_ty.clone(),
            info.method_poly_ty.clone(),
        );
        let call_local_idx = locals.len();
        locals.push(lir::Local {
            idx: call_local_idx,
            ty: TyScheme::from_mono(Ty::unit()),
        });
        block.push(lir::Inst::SetLocal(call_local_idx, lir::Value::Call(call)));
    }

    // 2. Drop fields in declaration order.
    emit_field_drops(
        &mut block,
        &mut locals,
        &mut symbols,
        lir::Variable::Local(self_local_idx),
        struct_ty,
        all_structs,
        drop_fn_map,
    );

    // 3. Return void.
    block.push(lir::Inst::Return(lir::Value::Empty));

    let cfg = lir::ControlFlowGraph::default();
    let mut func = lir::Func::new(
        drop_fn_name.clone(),
        fn_ty.clone(),
        vec![],
        symbols,
        cfg,
        None,
    );
    func.params = params;
    func.locals = locals;
    func.blocks = vec![block];

    DropFnInfo {
        func,
        name: drop_fn_name,
        ty: fn_ty,
        poly_ty,
    }
}

/// Emit DecRef/field-drop instructions for each field of a struct.
///
/// For ref-typed fields: GetField + DecRef.
/// For value-type struct fields with transitive refs: GetField, then
/// recurse to emit drops for the nested struct's fields.
fn emit_field_drops(
    block: &mut lir::Block,
    locals: &mut Vec<lir::Local>,
    symbols: &mut lir::SymbolSet,
    src_var: lir::Variable,
    struct_ty: &StructTy,
    all_structs: &HashMap<ItemPath, StructTy>,
    drop_fn_map: &HashMap<ItemPath, DropFnInfo>,
) {
    for (field_name, field_ty_scheme) in &struct_ty.fields {
        let field_mono = field_ty_scheme.mono();
        match field_mono {
            Ty::Ref(inner) | Ty::MutRef(inner) => {
                let kind = lir::RefCountKind::Strong;
                let drop_fn_ref = make_drop_func_ref(inner, drop_fn_map);
                if let Some(ref fr) = drop_fn_ref {
                    symbols.insert(fr.path.clone());
                }
                emit_getfield_decref(
                    block,
                    locals,
                    src_var.clone(),
                    field_name,
                    field_ty_scheme.clone(),
                    kind,
                    drop_fn_ref,
                );
            }
            Ty::IdRef(_) => {
                emit_getfield_decref(
                    block,
                    locals,
                    src_var.clone(),
                    field_name,
                    field_ty_scheme.clone(),
                    lir::RefCountKind::Weak,
                    None,
                );
            }
            // Value-type struct field — check if it transitively contains refs.
            Ty::Proj(path, _) | Ty::Const(path) => {
                if let Some(nested_struct) = all_structs.get(path) {
                    if has_ref_fields(nested_struct, all_structs) {
                        // Load the nested struct value, then recurse.
                        let field_local_idx = locals.len();
                        locals.push(lir::Local {
                            idx: field_local_idx,
                            ty: field_ty_scheme.clone(),
                        });
                        let get_field = lir::Value::GetField(lir::GetField {
                            src: src_var.clone(),
                            field: field_name.clone(),
                        });
                        block.push(lir::Inst::SetLocal(field_local_idx, get_field));

                        emit_field_drops(
                            block,
                            locals,
                            symbols,
                            lir::Variable::Local(field_local_idx),
                            nested_struct,
                            all_structs,
                            drop_fn_map,
                        );
                    }
                }
            }
            _ => {}
        }
    }
}

/// Emit a GetField + DecRef sequence for a single reference-typed field.
fn emit_getfield_decref(
    block: &mut lir::Block,
    locals: &mut Vec<lir::Local>,
    src_var: lir::Variable,
    field_name: &str,
    field_ty: TyScheme,
    kind: lir::RefCountKind,
    drop_fn: Option<lir::FuncRef>,
) {
    let field_local_idx = locals.len();
    locals.push(lir::Local {
        idx: field_local_idx,
        ty: field_ty,
    });

    let get_field = lir::Value::GetField(lir::GetField {
        src: src_var,
        field: field_name.to_string(),
    });
    block.push(lir::Inst::SetLocal(field_local_idx, get_field));

    let field_val = lir::Value::Atom(lir::Atom::Variable(lir::Variable::Local(field_local_idx)));
    block.push(lir::Inst::DecRef(field_val, kind, drop_fn));
}

/// Create a `FuncRef` for the drop function of a pointee type, if one exists.
fn make_drop_func_ref(
    pointee_ty: &Ty,
    drop_fn_map: &HashMap<ItemPath, DropFnInfo>,
) -> Option<lir::FuncRef> {
    let path = match pointee_ty {
        Ty::Const(p) | Ty::Proj(p, _) => p,
        _ => return None,
    };
    let info = drop_fn_map.get(path)?;
    let mut func_ref = lir::FuncRef::new(info.name.clone(), info.ty.clone());
    func_ref.poly_ty = info.poly_ty.clone();
    Some(func_ref)
}

/// Walk all functions in the program and patch `DecRef(val, Strong, None)`
/// instructions to include the appropriate drop function reference.
fn patch_decref_instructions(
    program: &mut lir::Program,
    drop_fn_map: &HashMap<ItemPath, DropFnInfo>,
) {
    for func in &mut program.funcs {
        // Collect local types for looking up pointee types.
        let local_tys: Vec<Ty> = func
            .locals
            .iter()
            .map(|loc| loc.ty.mono().clone())
            .collect();

        let mut new_symbols: Vec<Path> = vec![];

        for block in &mut func.blocks {
            for inst in block.iter_mut() {
                let lir::Inst::DecRef(value, lir::RefCountKind::Strong, drop_fn) = inst else {
                    continue;
                };

                // Already patched (e.g., inside a drop function itself).
                if drop_fn.is_some() {
                    continue;
                }

                // Get the local index from the value.
                let Some(local_idx) = value.local() else {
                    continue;
                };

                // Look up the local's type and unwrap the pointer.
                let Some(local_ty) = local_tys.get(local_idx) else {
                    continue;
                };
                let Some(pointee) = local_ty.unwrap_pointer() else {
                    continue;
                };

                // Check if the pointee type has a drop function.
                if let Some(func_ref) = make_drop_func_ref(pointee, drop_fn_map) {
                    new_symbols.push(func_ref.path.clone());
                    *drop_fn = Some(func_ref);
                }
            }
        }

        for sym in new_symbols {
            func.symbols.insert(sym);
        }
    }
}

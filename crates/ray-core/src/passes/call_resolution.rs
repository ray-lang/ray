use ray_shared::{
    collections::namecontext::NameContext,
    node_id::NodeId,
    pathlib::{ItemPath, Path},
    ty::Ty,
};
use ray_typing::{
    PatternKind, PatternRecord, TypeCheckInput,
    context::{AssignLhs, ExprKind},
    tyctx::{CallResolution, TyCtx},
    types::{Subst, TyScheme},
    unify::mgu,
};

pub fn run_call_resolution_pass(module: &TypeCheckInput, tcx: &mut TyCtx, ncx: &NameContext) {
    for (expr_id, record) in module.expr_records.iter() {
        match &record.kind {
            ExprKind::BinaryOp {
                trait_fqn,
                method_fqn,
                operator,
                ..
            }
            | ExprKind::UnaryOp {
                trait_fqn,
                method_fqn,
                operator,
                ..
            } => {
                resolve_op(*operator, trait_fqn, method_fqn, tcx);
            }
            ExprKind::Call { callee, .. } => {
                resolve_call(*callee, module, tcx);
            }
            ExprKind::Assign {
                lhs_pattern,
                lhs,
                rhs,
            } => {
                if let AssignLhs::Index { container, index } = lhs {
                    resolve_index_set(
                        *expr_id,
                        *lhs_pattern,
                        *container,
                        *index,
                        *rhs,
                        module,
                        tcx,
                        ncx,
                    );
                }
            }
            ExprKind::Index { container, index } => {
                resolve_index(*expr_id, *container, *index, tcx, ncx);
            }
            _ => {}
        }
    }
}

fn resolve_op(operator_id: NodeId, trait_fqn: &Path, method_fqn: &Path, tcx: &mut TyCtx) {
    if tcx.call_resolution(operator_id).is_some() {
        return;
    }

    let trait_item_path = ItemPath::from(trait_fqn);
    let Some(trait_ty) = tcx.get_trait_ty(&trait_item_path) else {
        return;
    };

    let Some(method_name) = method_fqn.name() else {
        return;
    };

    let Some(trait_field) = trait_ty.get_field(&method_name) else {
        return;
    };

    let poly_callee_ty = trait_field.ty.clone();
    let callee_ty = TyScheme::from_mono(tcx.get_ty(operator_id).cloned().unwrap());
    let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
        Ok((_, subst)) => subst,
        Err(_) => Subst::new(),
    };

    let base_fqn = method_fqn.clone();

    tcx.set_call_resolution(
        operator_id,
        CallResolution {
            base_fqn,
            poly_callee_ty,
            callee_ty,
            subst,
        },
    );
}

fn resolve_call(callee_id: NodeId, module: &TypeCheckInput, tcx: &mut TyCtx) {
    if tcx.call_resolution(callee_id).is_some() {
        return;
    }

    let Some(callee_kind) = module.expr_kind(callee_id) else {
        return;
    };

    let ExprKind::FieldAccess { recv, field } = callee_kind else {
        return;
    };

    if let Some((trait_ty, trait_field)) = tcx.resolve_trait_method(field) {
        let callee_ty = TyScheme::from_mono(tcx.get_ty(callee_id).cloned().unwrap());
        let poly_callee_ty = trait_field.ty.clone();
        let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
            Ok((_, subst)) => subst,
            Err(_) => Subst::new(),
        };

        let base_fqn = trait_ty.path.append(field);

        tcx.set_call_resolution(
            callee_id,
            CallResolution {
                base_fqn,
                poly_callee_ty,
                callee_ty,
                subst,
            },
        );
        return;
    }

    let Some(recv_ty) = tcx.get_ty(*recv) else {
        return;
    };

    let recv_fqn = match recv_ty {
        Ty::Ref(inner) => inner.get_path().with_names_only(),
        _ => recv_ty.get_path().with_names_only(),
    };
    log::debug!("[call_resolution] recv_fqn: {}", recv_fqn);
    if let Some((_, impl_field)) = tcx.resolve_inherent_method(&recv_fqn, field) {
        let poly_callee_ty = impl_field.scheme.clone().unwrap();
        let callee_ty = TyScheme::from_mono(tcx.get_ty(callee_id).cloned().unwrap());
        let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
            Ok((_, subst)) => subst,
            Err(_) => Subst::new(),
        };

        let base_fqn = impl_field.path.clone();
        log::debug!(
            "[call_resolution] inherent method: base_fqn = {}, poly_callee_ty = {}, callee_ty = {}, subst = {}",
            base_fqn,
            poly_callee_ty,
            callee_ty,
            subst
        );
        tcx.set_call_resolution(
            callee_id,
            CallResolution {
                base_fqn,
                poly_callee_ty,
                callee_ty,
                subst,
            },
        );
    }
}

fn resolve_index(
    index_expr_id: NodeId,
    container_id: NodeId,
    index_id: NodeId,
    tcx: &mut TyCtx,
    ncx: &NameContext,
) {
    if tcx.call_resolution(index_expr_id).is_some() {
        return;
    }

    let trait_fqn = ItemPath::from(&ncx.builtin_ty("Index"));
    let Some(trait_ty) = tcx.get_trait_ty(&trait_fqn) else {
        return;
    };

    let method_name = "get".to_string();
    let Some(trait_field) = trait_ty.get_field(&method_name) else {
        return;
    };

    let poly_callee_ty = trait_field.ty.clone();

    let container_ty = tcx.ty_of(container_id).mono().clone();
    let index_ty = tcx.ty_of(index_id).mono().clone();
    let result_ty = tcx.ty_of(index_expr_id).mono().clone();

    let recv_ty = Ty::ref_of(container_ty);
    let callee_ty = TyScheme::from_mono(Ty::Func(vec![recv_ty, index_ty], Box::new(result_ty)));

    let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
        Ok((_, subst)) => subst,
        Err(_) => Subst::new(),
    };

    let base_fqn = trait_ty.path.append(&method_name);

    tcx.set_call_resolution(
        index_expr_id,
        CallResolution {
            base_fqn,
            poly_callee_ty,
            callee_ty,
            subst,
        },
    );
}

fn resolve_index_set(
    assign_expr_id: NodeId,
    lhs_pattern_id: NodeId,
    _container_binding: ray_shared::local_binding::LocalBindingId,
    index_id: NodeId,
    rhs_id: NodeId,
    module: &TypeCheckInput,
    tcx: &mut TyCtx,
    ncx: &NameContext,
) {
    if tcx.call_resolution(assign_expr_id).is_some() {
        return;
    }

    let trait_fqn = ncx.builtin_ty("Index");
    let Some(trait_ty) = tcx.get_trait_ty(&ItemPath::from(trait_fqn)) else {
        return;
    };

    let method_name = "set".to_string();
    let Some(trait_field) = trait_ty.get_field(&method_name) else {
        return;
    };

    let poly_callee_ty = trait_field.ty.clone();

    // Get container type from pattern records since we can't look up LocalBindingId
    // in the DefId-keyed binding_records
    let container_ty = module
        .pattern_records
        .get(&lhs_pattern_id)
        .and_then(|record| match &record.kind {
            ray_typing::PatternKind::Index { container, .. } => tcx.get_ty(*container),
            _ => None,
        })
        .cloned()
        .unwrap_or_else(|| Ty::Var(tcx.new_schema_var()));

    let index_ty = tcx.ty_of(index_id).mono().clone();
    let elem_ty = tcx.ty_of(rhs_id).mono().clone();

    let recv_ty = Ty::ref_of(container_ty);
    let ret_ty = Ty::nilable(elem_ty.clone());
    let callee_ty =
        TyScheme::from_mono(Ty::Func(vec![recv_ty, index_ty, elem_ty], Box::new(ret_ty)));

    let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
        Ok((_, subst)) => subst,
        Err(_) => Subst::new(),
    };

    let base_fqn = trait_ty.path.append(&method_name);

    tcx.set_call_resolution(
        assign_expr_id,
        CallResolution {
            base_fqn,
            poly_callee_ty,
            callee_ty,
            subst,
        },
    );

    // For nested index assignment like `l[i][j] = ...`, the receiver for the
    // outer `Index::set` is itself a `Pattern::Index` that must be lowered as
    // a value via `Index::get`. Call resolution is stored by NodeId, so we
    // pre-resolve any nested index patterns in the LHS container chain.
    if let Some(PatternRecord {
        kind: PatternKind::Index { container, .. },
        ..
    }) = module.pattern_records.get(&lhs_pattern_id)
    {
        resolve_index_pattern_chain(*container, module, tcx, ncx);
    }
}

fn resolve_index_pattern_chain(
    pattern_id: NodeId,
    module: &TypeCheckInput,
    tcx: &mut TyCtx,
    ncx: &NameContext,
) {
    let Some(record) = module.pattern_records.get(&pattern_id) else {
        return;
    };

    if let PatternKind::Index { container, index } = &record.kind {
        resolve_index_pattern_get(pattern_id, *container, *index, tcx, ncx);
        resolve_index_pattern_chain(*container, module, tcx, ncx);
    }
}

fn resolve_index_pattern_get(
    pattern_id: NodeId,
    container_id: NodeId,
    index_id: NodeId,
    tcx: &mut TyCtx,
    ncx: &NameContext,
) {
    if tcx.call_resolution(pattern_id).is_some() {
        return;
    }

    let trait_fqn = ncx.builtin_ty("Index");
    let Some(trait_ty) = tcx.get_trait_ty(&ItemPath::from(&trait_fqn)) else {
        return;
    };

    let method_name = "get".to_string();
    let Some(trait_field) = trait_ty.get_field(&method_name) else {
        return;
    };

    let poly_callee_ty = trait_field.ty.clone();

    let container_ty = tcx.ty_of(container_id).mono().clone();
    let index_ty = tcx.ty_of(index_id).mono().clone();
    let result_ty = tcx.ty_of(pattern_id).mono().clone();

    let recv_ty = Ty::ref_of(container_ty);
    let callee_ty = TyScheme::from_mono(Ty::Func(vec![recv_ty, index_ty], Box::new(result_ty)));

    let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
        Ok((_, subst)) => subst,
        Err(_) => Subst::new(),
    };

    let base_fqn = trait_ty.path.append(&method_name);

    tcx.set_call_resolution(
        pattern_id,
        CallResolution {
            base_fqn,
            poly_callee_ty,
            callee_ty,
            subst,
        },
    );
}

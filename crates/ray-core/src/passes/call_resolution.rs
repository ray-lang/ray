use ray_shared::node_id::NodeId;
use ray_shared::pathlib::Path;
use ray_typing::ModuleInput;
use ray_typing::context::ExprKind;
use ray_typing::tyctx::{CallResolution, TyCtx};
use ray_typing::types::{Subst, TyScheme};
use ray_typing::unify::mgu;

pub fn run_call_resolution_pass(module: &ModuleInput, tcx: &mut TyCtx) {
    for (_, record) in module.expr_records.iter() {
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
            _ => {}
        }
    }
}

fn resolve_op(operator_id: NodeId, trait_fqn: &Path, method_fqn: &Path, tcx: &mut TyCtx) {
    if tcx.call_resolution(operator_id).is_some() {
        return;
    }

    let Some(trait_ty) = tcx.get_trait_ty(trait_fqn) else {
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

fn resolve_call(callee_id: NodeId, module: &ModuleInput, tcx: &mut TyCtx) {
    if tcx.call_resolution(callee_id).is_some() {
        return;
    }

    let Some(callee_kind) = module.expr_kind(callee_id) else {
        return;
    };

    let ExprKind::FieldAccess { field, .. } = callee_kind else {
        return;
    };

    let Some((trait_ty, trait_field)) = tcx.resolve_trait_method(field) else {
        return;
    };

    let poly_callee_ty = trait_field.ty.clone();
    let callee_ty = TyScheme::from_mono(tcx.get_ty(callee_id).cloned().unwrap());
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
}

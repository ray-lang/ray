use ray_shared::{pathlib::Path, ty::Ty, utils::map_join};
use ray_typing::types::TyScheme;

pub fn fn_name(base: &Path, ty: &TyScheme) -> Path {
    let (_, _, param_tys, ret_ty) = ty
        .try_borrow_fn()
        .expect(&format!("expected a function type but found {}", ty));
    base.with_names_only()
        .append_func_type(param_tys.clone(), ret_ty.clone())
}

pub fn fn_ty(param_tys: &[Ty], ret_ty: &Ty) -> String {
    format!(
        "<({}):{:#}>",
        map_join(param_tys, ",", |t| format!("{:#}", t)),
        ret_ty
    )
}

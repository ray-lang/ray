use ray_shared::{pathlib::Path, utils::map_join};

use ray_typing::ty::TyScheme;

pub fn fn_name(base: &Path, ty: &TyScheme) -> Path {
    let (_, _, param_tys, ret_ty) = ty.try_borrow_fn().unwrap();
    base.with_names_only().append_func_type(format!(
        "<({}):{:#}>",
        map_join(param_tys, ",", |t| format!("{:#}", t)),
        ret_ty
    ))
}

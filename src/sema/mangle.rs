use crate::{ast::Path, typing::ty::Ty, utils::map_join};

pub fn fn_name(base: &Path, ty: &Ty) -> Path {
    let (_, _, param_tys, ret_ty) = ty.try_borrow_fn().unwrap();
    base.without_func_type().append_func_type(format!(
        "<({}):{:#}>",
        map_join(param_tys, ",", |t| format!("{:#}", t)),
        ret_ty
    ))
}

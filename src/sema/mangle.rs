use crate::{lir, typing::ty::Ty, utils::map_join};

pub fn mangle(s: &str) -> String {
    s.replace(" ", "")
}

pub fn fn_name<S: ToString>(name: S, ty: &Ty) -> String {
    let (_, _, param_tys, ret_ty) = ty.try_borrow_fn().unwrap();
    let mut name = name.to_string();
    name = format!(
        "{}::<({}):{:#}>",
        name,
        map_join(param_tys, ",", |t| format!("{:#}", t)),
        ret_ty
    );
    mangle(&name)
}

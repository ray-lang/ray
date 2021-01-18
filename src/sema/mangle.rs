use crate::{lir, utils::map_join};

pub fn mangle(s: &str) -> String {
    s.replace(" ", "")
}

pub fn fn_name(name: &str, ty: &lir::FnType) -> String {
    let mut name = name.to_string();
    name = format!(
        "{}({})",
        name,
        map_join(&ty.param_tys, ",", |t| format!("{:#}", t))
    );
    mangle(&name)
}

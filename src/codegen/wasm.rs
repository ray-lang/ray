pub use parity_wasm::builder::*;
pub use parity_wasm::elements::*;

use crate::typing::ty::Ty;

pub fn to_wasm_ty(ty: &Ty) -> ValueType {
    match ty {
        Ty::Never => todo!("to_wasm_ty: {}", ty),
        Ty::Any => ValueType::I32,
        Ty::Var(_) => todo!("to_wasm_ty: {}", ty),
        Ty::Tuple(_) => ValueType::I32,
        Ty::Union(_) => todo!("to_wasm_ty: {}", ty),
        Ty::Func(_, _) => todo!("to_wasm_ty: {}", ty),
        Ty::Ptr(_) => ValueType::I32,
        Ty::Projection(s, ..) => match s.as_str() {
            "i8" | "i16" | "i32" | "int" | "u8" | "u16" | "u32" | "uint" => ValueType::I32,
            "u64" | "i64" => ValueType::I64,
            _ => ValueType::I32, // everything else are just address types
        },
        Ty::Cast(_, _) => todo!("to_wasm_ty: {}", ty),
        Ty::Qualified(_, _) => todo!("to_wasm_ty: {}", ty),
        Ty::All(_, _) => todo!("to_wasm_ty: {}", ty),
    }
}

pub fn to_fn_ty(param_tys: &Vec<Ty>, ret_ty: &Ty) -> Type {
    let params = param_tys.iter().map(|t| to_wasm_ty(t)).collect();
    let results = if !ret_ty.is_unit() {
        vec![to_wasm_ty(ret_ty)]
    } else {
        vec![]
    };
    Type::Function(FunctionType::new(params, results))
}

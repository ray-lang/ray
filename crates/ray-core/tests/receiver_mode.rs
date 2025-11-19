#![cfg(test)]

use ray_core::{
    ast::Path,
    typing::ty::{ReceiverMode, Ty},
};

fn ty_var(name: &str) -> Ty {
    Ty::var(Path::from(name))
}

#[test]
fn receiver_mode_static_is_none() {
    let base = ty_var("test::Trait::Self");
    let param_tys = vec![base.clone(), Ty::ptr(base.clone())];

    let mode = ReceiverMode::from_signature(&base, &param_tys, true);
    assert_eq!(mode, ReceiverMode::None);
}

#[test]
fn receiver_mode_value_for_self_param() {
    let base = ty_var("test::Trait::Self");
    let param_tys = vec![base.clone()];

    let mode = ReceiverMode::from_signature(&base, &param_tys, false);
    assert_eq!(mode, ReceiverMode::Value);
}

#[test]
fn receiver_mode_ptr_for_ptr_self_param() {
    let base = ty_var("test::Trait::Self");
    let param_tys = vec![Ty::ptr(base.clone())];

    let mode = ReceiverMode::from_signature(&base, &param_tys, false);
    assert_eq!(mode, ReceiverMode::Ptr);
}

#[test]
fn receiver_mode_with_pointer_self_instantiation() {
    // Self is already a pointer type (e.g., impl T[*Foo]).
    let inner = Ty::con("test::Foo");
    let base = Ty::ptr(inner.clone());

    // Value receiver: self: Self (here Self = *Foo).
    let value_params = vec![base.clone()];
    let value_mode = ReceiverMode::from_signature(&base, &value_params, false);
    assert_eq!(value_mode, ReceiverMode::Value);

    // Pointer receiver: self: *Self (here self : **Foo).
    let ptr_params = vec![Ty::ptr(base.clone())];
    let ptr_mode = ReceiverMode::from_signature(&base, &ptr_params, false);
    assert_eq!(ptr_mode, ReceiverMode::Ptr);
}


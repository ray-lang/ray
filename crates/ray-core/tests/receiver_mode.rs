#![cfg(test)]

use ray_shared::{pathlib::Path, ty::Ty};
use ray_typing::types::ReceiverMode;

fn ty_var(name: &str) -> Ty {
    Ty::var(Path::from(name))
}

#[test]
fn receiver_mode_static_is_none() {
    let base = ty_var("test::Trait::Self");
    let param_tys = vec![base.clone(), Ty::ref_of(base.clone())];

    let mode = ReceiverMode::from_signature(&param_tys, true);
    assert_eq!(mode, ReceiverMode::None);
}

#[test]
fn receiver_mode_value_for_self_param() {
    let base = ty_var("test::Trait::Self");
    let param_tys = vec![base.clone()];

    let mode = ReceiverMode::from_signature(&param_tys, false);
    assert_eq!(mode, ReceiverMode::Value);
}

#[test]
fn receiver_mode_ptr_for_ptr_self_param() {
    let base = ty_var("test::Trait::Self");
    let param_tys = vec![Ty::ref_of(base.clone())];

    let mode = ReceiverMode::from_signature(&param_tys, false);
    assert_eq!(mode, ReceiverMode::Ptr);
}

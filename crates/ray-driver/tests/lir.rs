#![cfg(test)]

mod utils;

use std::convert::TryInto;

use ray_core::lir::{Inst, Program, Value};
use ray_typing::types::Ty;
use utils::test_build;

#[test]
fn lir_generation_simple_function() {
    let src = r#"
        fn id(x: u32) -> u32 { x }
        pub fn main() -> u32 { id(1u32) }
    "#;

    let frontend = test_build(src).expect("frontend build should succeed");
    eprintln!(
        "structs: {:?}",
        frontend
            .tcx
            .global_env
            .structs
            .keys()
            .cloned()
            .collect::<Vec<_>>()
    );
    assert!(
        frontend.errors.is_empty(),
        "expected no frontend errors, got {:?}",
        frontend.errors
    );
    for error in &frontend.errors {
        eprintln!("frontend error: {:?}", error);
    }

    let program = Program::generate(
        &frontend.module,
        &frontend.tcx,
        &frontend.srcmap,
        &frontend.bindings,
        &frontend.closure_analysis,
        frontend.libs.clone(),
    )
    .expect("lir generation should succeed");
    // Sanity check: at least one function emitted (main + id)
    assert!(
        !program.funcs.is_empty(),
        "expected program to contain functions"
    );
}

#[test]
fn lir_generation_closure_and_struct() {
    let src = r#"
@intrinsic extern fn u32_add(a: u32, b: u32) -> u32

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

impl Add[u32, u32, u32] {
    fn +(lhs: u32, rhs: u32) -> u32 => u32_add(lhs, rhs)
}

struct Pair { x: u32, y: u32 }

pub fn main() -> u32 {
    p = Pair { x: 1u32, y: 2u32 }
    add = (a, b) => a + b
    add(p.x, p.y)
}
"#;

    let frontend = test_build(src).expect("frontend build should succeed");
    assert!(
        frontend.errors.is_empty(),
        "expected no frontend errors, got {:?}",
        frontend.errors
    );

    let program = Program::generate(
        &frontend.module,
        &frontend.tcx,
        &frontend.srcmap,
        &frontend.bindings,
        &frontend.closure_analysis,
        frontend.libs.clone(),
    )
    .expect("lir generation should succeed");

    let user_main_idx: usize = program
        .user_main_idx
        .try_into()
        .expect("user main index should be set");
    let main_func = &program.funcs[user_main_idx];

    let mut saw_pair_literal = false;
    let mut saw_closure_call = false;
    for block in &main_func.value.blocks {
        for inst in block.iter() {
            match inst {
                Inst::StructInit(_, struct_ty) => {
                    if struct_ty.path.to_string().contains("Pair") {
                        saw_pair_literal = true;
                    }
                }
                Inst::SetLocal(_, value) => {
                    if let Value::Call(call) = value {
                        if call.fn_ref.is_some() {
                            saw_closure_call = true;
                            assert_eq!(
                                call.args.len(),
                                3,
                                "closure call should pass env + two arguments"
                            );
                        }
                    }
                }
                _ => {}
            }
        }
    }

    assert!(
        saw_pair_literal,
        "expected Pair struct literal to lower through StructInit\n--- LIR Program ---\n{}",
        program
    );
    assert!(
        saw_closure_call,
        "expected Call::new_ref instruction when invoking the lambda\n--- LIR Program ---\n{:#?}",
        program
    );

    let closure_func = program
        .funcs
        .iter()
        .find(|func| func.value.name.to_string().contains("$closure_"))
        .expect("lowering should emit a dedicated closure function");
    assert_eq!(
        closure_func.value.params.len(),
        3,
        "closure should accept env + two parameters"
    );
    let env_param = closure_func
        .value
        .params
        .first()
        .expect("closure function must start with env parameter");
    match &env_param.ty {
        Ty::RawPtr(inner) => assert_eq!(
            **inner,
            Ty::u8(),
            "env parameter should be backed by rawptr, got {}",
            inner
        ),
        other => panic!(
            "expected closure env parameter to be a rawptr[u8], got {}",
            other
        ),
    }
}

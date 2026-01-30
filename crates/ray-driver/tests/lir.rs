#![cfg(test)]

mod utils;

use std::convert::TryInto;

use ray_codegen::lir::{Inst, Program, Value};
use ray_shared::ty::Ty;
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
        &frontend.ncx,
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
        &frontend.ncx,
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

#[test]
fn lir_generation_index_operator() {
    let src = r#"
trait Index['a, 'el, 'idx] {
    fn get(self: *'a, idx: 'idx) -> 'el?
}

struct Box { v: u32 }

impl Index[Box, u32, u32] {
    fn get(self: *Box, idx: u32) -> u32? {
        nil
    }
}

pub fn main() -> u32 {
    b = Box { v: 1u32 }
    x = b[0u32]
    0u32
}
"#;

    let frontend = test_build(src).expect("frontend build should succeed");
    assert!(
        frontend.errors.is_empty(),
        "expected no frontend errors, got {:?}",
        frontend.errors
    );

    Program::generate(
        &frontend.module,
        &frontend.tcx,
        &frontend.ncx,
        &frontend.srcmap,
        &frontend.bindings,
        &frontend.closure_analysis,
        frontend.libs.clone(),
    )
    .expect("lir generation should succeed");
}

#[test]
fn lir_generation_index_assignment() {
    let src = r#"
trait Index['a, 'el, 'idx] {
    fn get(self: *'a, idx: 'idx) -> 'el?
    fn set(self: *'a, idx: 'idx, el: 'el) -> 'el?
}

struct Box { v: u32 }

impl Index[Box, u32, u32] {
    fn get(self: *Box, idx: u32) -> u32? { nil }
    fn set(self: *Box, idx: u32, el: u32) -> u32? { nil }
}

pub fn main() -> u32 {
    b = Box { v: 1u32 }
    b[0u32] = 2u32
    0u32
}
"#;

    let frontend = test_build(src).expect("frontend build should succeed");
    assert!(
        frontend.errors.is_empty(),
        "expected no frontend errors, got {:?}",
        frontend.errors
    );

    Program::generate(
        &frontend.module,
        &frontend.tcx,
        &frontend.ncx,
        &frontend.srcmap,
        &frontend.bindings,
        &frontend.closure_analysis,
        frontend.libs.clone(),
    )
    .expect("lir generation should succeed");
}

#[test]
fn lir_generation_field_assignment() {
    let src = r#"
struct Pair { x: u32, y: u32 }

pub fn main() -> u32 {
    p = Pair { x: 1u32, y: 2u32 }
    p.x = 3u32
    0u32
}
"#;

    let frontend = test_build(src).expect("frontend build should succeed");
    assert!(
        frontend.errors.is_empty(),
        "expected no frontend errors, got {:?}",
        frontend.errors
    );

    Program::generate(
        &frontend.module,
        &frontend.tcx,
        &frontend.ncx,
        &frontend.srcmap,
        &frontend.bindings,
        &frontend.closure_analysis,
        frontend.libs.clone(),
    )
    .expect("lir generation should succeed");
}

#[test]
fn lir_generation_while_break_exits_loop() {
    let src = r#"
pub fn main() -> u32 {
    mut x = 0u32
    while true {
        x = 1u32
        break
    }
    x = 2u32
    x
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
        &frontend.ncx,
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

    let loop_header = main_func
        .value
        .blocks
        .iter()
        .find(|block| block.is_loop_header())
        .expect("expected at least one loop header block");
    let cond_label = loop_header.label();

    let Some(Inst::If(loop_if)) = loop_header.last() else {
        panic!(
            "expected loop header to end with Inst::If\n--- LIR Program ---\n{}",
            program
        );
    };
    let break_label = loop_if.else_label;

    let break_block = main_func
        .value
        .blocks
        .iter()
        .find(|block| block.label() == break_label)
        .expect("expected loop break target block to exist");
    let Some(Inst::Goto(after_label)) = break_block.last().cloned() else {
        panic!(
            "expected break target block to end with Inst::Goto\n--- LIR Program ---\n{}",
            program
        );
    };

    let after_block = main_func
        .value
        .blocks
        .iter()
        .find(|block| block.label() == after_label)
        .expect("expected post-loop block to exist");
    assert!(
        after_block
            .markers()
            .iter()
            .any(|marker| matches!(marker, ray_codegen::lir::ControlMarker::End(label) if *label == cond_label)),
        "expected post-loop block to be marked as End({}), got markers={:?}\n--- LIR Program ---\n{}",
        cond_label,
        after_block.markers(),
        program
    );
}

#[test]
fn lir_generation_for_loop_calls_iter_next() {
    let src = r#"
trait Iter['it, 'el] {
    fn next(self: *'it) -> 'el?
}

trait Iterable['c, 'it, 'el] {
    fn iter(self: *'c) -> 'it
}

struct Counter { start: u32 }
struct CounterIter { done: bool }

impl Iterable[Counter, CounterIter, u32] {
    fn iter(self: *Counter) -> CounterIter {
        CounterIter { done: false }
    }
}

impl Iter[CounterIter, u32] {
    fn next(self: *CounterIter) -> u32? { nil }
}

pub fn main() -> u32 {
    c = Counter { start: 0u32 }
    for x in c {
        y = x
    }
    0u32
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
        &frontend.ncx,
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

    let mut saw_iter = false;
    let mut saw_next = false;

    for block in &main_func.value.blocks {
        for inst in block.iter() {
            if let Inst::SetLocal(_, value) = inst {
                if let Value::Call(call) = value {
                    let name = call.fn_name.to_string();
                    if name.contains("Iterable::iter") {
                        saw_iter = true;
                    }
                    if name.contains("Iter::next") {
                        saw_next = true;
                    }
                }
            }
        }
    }

    assert!(
        saw_iter,
        "expected `for` lowering to call Iterable::iter\n--- LIR Program ---\n{}",
        program
    );
    assert!(
        saw_next,
        "expected `for` lowering to call Iter::next\n--- LIR Program ---\n{}",
        program
    );
}

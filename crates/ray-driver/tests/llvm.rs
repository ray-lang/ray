#![cfg(test)]

mod utils;

use ray_codegen::{codegen::llvm::emit_module_ir, lir::Program};
use ray_core::target::Target;
use ray_shared::optlevel::OptLevel;
use utils::{enable_debug_logs, test_build};

#[test]
fn llvm_emits_closure_env_and_function() {
    let src = r#"
@intrinsic extern fn u32_add(a: u32, b: u32) -> u32

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

impl Add[u32, u32, u32] {
    fn +(lhs: u32, rhs: u32) -> u32 => u32_add(lhs, rhs)
}

pub fn main() -> u32 {
    bias = 10u32
    add = (value) => bias + value
    add(32u32)
}
"#;

    let frontend = test_build(src).expect("frontend build should succeed");
    assert!(
        frontend.errors.is_empty(),
        "expected no frontend errors, got {:?}",
        frontend.errors
    );

    let mut program = Program::generate(
        &frontend.module,
        &frontend.tcx,
        &frontend.ncx,
        &frontend.srcmap,
        &frontend.bindings,
        &frontend.closure_analysis,
        frontend.libs.clone(),
    )
    .expect("lir generation should succeed");
    program.monomorphize();

    eprintln!("---------- LIR ----------\n{}", program);

    enable_debug_logs();
    let ir = emit_module_ir(
        &program,
        &frontend.tcx,
        &frontend.srcmap,
        &Target::default(),
        OptLevel::O0,
    );

    eprintln!("---------- LLVM ----------\n{}", ir);

    let env_decl = ir
        .lines()
        .find(|line| line.contains("__closure_env_") && line.contains("type"))
        .expect("closure environment struct should be declared");
    assert!(
        env_decl.contains("i32"),
        "closure env should carry captured bias, saw `{}`",
        env_decl
    );

    assert!(
        ir.contains("$u24closure_"),
        "expected lowered closure function in LLVM IR:\n{}",
        ir
    );

    assert!(
        ir.contains("call i32 %"),
        "expected the closure call to appear in LLVM IR:\n{}",
        ir
    );

    assert!(
        ir.contains("getelementptr %\"test::__closure_env_"),
        "expected closure body to read from the environment struct:\n{}",
        ir
    );
}

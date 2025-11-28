#![cfg(test)]

mod utils;

use utils::{TestBuildOptions, test_build_with_options};

#[test]
fn value_receiver_methods_typecheck_for_value_and_pointer() {
    let src = r#"
trait Value['a] {
    fn get(self: 'a) -> int
}

impl Value[int] {
    fn get(self: int) -> int {
        1
    }
}

fn call_on_value(x: int) -> int {
    x.get()
}

fn call_on_ptr(p: *int) -> int {
    p.get()
}
"#;

    test_build_with_options(src, TestBuildOptions { minimal_core: true }).unwrap_or_else(|errs| {
        panic!(
            "expected type checking to succeed, but found errors: {:#?}",
            errs
        );
    });
}

#[test]
fn ptr_receiver_methods_typecheck_for_value_and_pointer() {
    let src = r#"
trait ByRef['a] {
    fn touch(self: *'a)
}

impl ByRef[int] {
    fn touch(self: *int) {}
}

fn call_on_value(x: int) {
    x.touch()
}

fn call_on_ptr(p: *int) {
    p.touch()
}
"#;

    test_build_with_options(src, TestBuildOptions { minimal_core: true }).unwrap_or_else(|errs| {
        panic!(
            "expected type checking to succeed, but found errors: {:#?}",
            errs
        );
    });
}

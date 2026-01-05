use ray_core::{
    passes::{FrontendPassManager, binding::BindingPassOutput},
    sema::ModuleBuilder,
};
use ray_shared::{
    pathlib::Path,
    ty::{Ty, TyVar},
    utils::join,
};
use ray_typing::{
    NodeBinding, TypeCheckResult, TypecheckOptions,
    constraints::Predicate,
    tyctx::TyCtx,
    types::{Subst, Substitutable as _, TyScheme},
};

#[allow(dead_code)]
fn enable_debug_logs() {
    fern::Dispatch::new()
        .level(log::LevelFilter::Debug)
        .chain(std::io::stderr())
        .apply()
        .unwrap();
}

fn typecheck_src(module_name: &str, src: &str) -> (Path, TypeCheckResult, TyCtx) {
    let (module_path, result, tcx, _) = typecheck_src_with_bindings(module_name, src);
    (module_path, result, tcx)
}

fn typecheck_src_with_bindings(
    module_name: &str,
    src: &str,
) -> (Path, TypeCheckResult, TyCtx, BindingPassOutput) {
    let module_path = Path::from(module_name);
    let mut builder_result =
        ModuleBuilder::from_src(src, module_path.clone()).expect("module should build");

    let tc_options = TypecheckOptions::default();
    let pass_manager = FrontendPassManager::new(
        &builder_result.module,
        &builder_result.srcmap,
        &mut builder_result.tcx,
    );
    let (binding_output, _, result) = pass_manager.run_passes(&builder_result.ncx, tc_options);

    let tcx = builder_result.tcx;
    (module_path, result, tcx, binding_output)
}

fn assert_typechecks(test_name: &str, result: &TypeCheckResult) {
    assert!(
        result.errors.is_empty(),
        "typechecker reported errors for {}: {:?}\n{}",
        test_name,
        result.errors,
        join(&result.errors, "\n")
    );
}

fn assert_scheme_eq(
    tcx: &TyCtx,
    module_path: &Path,
    binding: &str,
    expected_vars: &[TyVar],
    expected_ty: Ty,
    expected_predicates: &[Predicate],
) {
    let subpath = Path::from(binding);
    let path = module_path.append_path(subpath);
    let scheme = tcx.schemes().get(&path).unwrap_or_else(|| {
        panic!(
            "typechecker did not produce an exported scheme for {}: {:?}",
            path,
            tcx.schemes()
        )
    });

    assert_scheme_matches(
        scheme,
        &path.to_string(),
        expected_vars,
        &expected_ty,
        expected_predicates,
    );
}

fn assert_local_scheme_eq(
    tcx: &TyCtx,
    bindings: &BindingPassOutput,
    module_path: &Path,
    binding: &str,
    expected_vars: &[TyVar],
    expected_ty: Ty,
    expected_predicates: &[Predicate],
) {
    let relative = Path::from(binding);
    let full = module_path.append_path(relative.clone());
    let binding_id = bindings
        .value_bindings
        .get(&full)
        .copied()
        .or_else(|| bindings.value_bindings.get(&relative).copied())
        .or_else(|| {
            bindings.binding_records.iter().find_map(|(id, record)| {
                record.path.as_ref().and_then(|p| {
                    if p == &full || p == &relative {
                        Some(*id)
                    } else {
                        None
                    }
                })
            })
        })
        .unwrap_or_else(|| {
            panic!(
                "binding pass did not record binding {}. available: {:?}",
                full, bindings.value_bindings
            )
        });

    let node_id = bindings
        .node_bindings
        .iter()
        .find_map(|(node, id)| match id {
            NodeBinding::Def(id) if *id == binding_id => Some(*node),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no node mapped for binding {}", full));

    let scheme = tcx.node_schemes.get(&node_id).unwrap_or_else(|| {
        panic!(
            "typechecker did not record a scheme for node {:?} ({})",
            node_id, full
        )
    });

    assert_scheme_matches(
        scheme,
        &full.to_string(),
        expected_vars,
        &expected_ty,
        expected_predicates,
    );
}

fn assert_local_ty_eq(
    tcx: &TyCtx,
    bindings: &BindingPassOutput,
    module_path: &Path,
    binding: &str,
    expected_ty: Ty,
) {
    assert_local_scheme_eq(tcx, bindings, module_path, binding, &[], expected_ty, &[]);
}

fn assert_scheme_matches(
    scheme: &TyScheme,
    label: &str,
    expected_vars: &[TyVar],
    expected_ty: &Ty,
    expected_predicates: &[Predicate],
) {
    assert_eq!(
        scheme.vars.len(),
        expected_vars.len(),
        "quantified var count mismatch for {}: {}",
        label,
        scheme,
    );

    let mut actual_vars = scheme.vars.clone();
    actual_vars.sort();
    let mut expected_vars_sorted = expected_vars.to_vec();
    expected_vars_sorted.sort();

    let mut renaming = Subst::new();
    for (actual, expected) in actual_vars.iter().zip(expected_vars_sorted.iter()) {
        if actual != expected {
            renaming.insert(expected.clone(), Ty::Var(actual.clone()));
        }
    }

    let mut expected_ty = expected_ty.clone();
    expected_ty.apply_subst(&renaming);
    assert_eq!(scheme.ty, expected_ty, "type mismatch for {}", label);

    let mut expected_preds = expected_predicates.to_vec();
    for pred in expected_preds.iter_mut() {
        pred.apply_subst(&renaming);
    }
    assert_eq!(
        scheme.qualifiers.len(),
        expected_preds.len(),
        "qualifiers mismatch for {}:\n  expected={:?}\n  found={:?}",
        label,
        expected_preds,
        scheme.qualifiers,
    );
    assert!(
        expected_preds
            .iter()
            .all(|pred| scheme.qualifiers.contains(pred)),
        "qualifiers mismatch for {}:\n  expected={:?}\n  found={:?}",
        label,
        expected_preds,
        scheme.qualifiers,
    )
}

#[test]
fn typechecks_simple_u32_id_function() {
    let src = r#"
        fn id(x: u32) -> u32 { x }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_simple_u32_id_function", src);
    assert_typechecks("typechecks_simple_u32_id_function", &result);
    let expected_ty = Ty::func(vec![Ty::u32()], Ty::u32());
    assert_scheme_eq(&tcx, &module_path, "id", &[], expected_ty, &[]);
}

#[test]
fn typechecks_unannotated_id_function() {
    let src = r#"
        fn inferred_id(x) { x }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_unannotated_id_function", src);
    assert_typechecks("typechecks_unannotated_id_function", &result);
    let var = TyVar::new("?s0");
    let vars = vec![var.clone()];
    let ty = Ty::Var(var);
    let expected_ty = Ty::func(vec![ty.clone()], ty);
    assert_scheme_eq(&tcx, &module_path, "inferred_id", &vars, expected_ty, &[]);
}

#[test]
fn typechecks_unannotated_bool_literal_function() {
    let src = r#"
        fn inferred_bool() { true }
    "#;

    let (module_path, result, tcx) =
        typecheck_src("typechecks_unannotated_bool_literal_function", src);
    assert_typechecks("typechecks_unannotated_bool_literal_function", &result);
    let expected_ty = Ty::func(vec![], Ty::bool());
    assert_scheme_eq(&tcx, &module_path, "inferred_bool", &[], expected_ty, &[]);
}

#[test]
fn records_call_resolution_for_unary_ops() {
    let src = r#"
        @intrinsic extern fn i32_neg(a: i32) -> i32
        trait Neg['a, 'b] { fn -(self: 'a) -> 'b }
        impl Neg[i32, i32] {
            fn -(self: i32) -> i32 => i32_neg(self)
        }
        fn main() {
            x = 1i32
            a = -x
        }
    "#;

    let (_, result, tcx) = typecheck_src("records_call_resolution_for_unary_ops", src);
    assert_typechecks("records_call_resolution_for_unary_ops", &result);

    let expected = Path::from("records_call_resolution_for_unary_ops::Neg::-");
    assert!(
        tcx.call_resolutions()
            .values()
            .any(|resolution| resolution.base_fqn.with_names_only() == expected),
        "expected a call resolution for unary - via {}, got: {:?}",
        expected,
        tcx.call_resolutions()
    );
}

#[test]
fn typechecks_generic_id_with_class_constraint() {
    let src = r#"
        trait Int['t] {}
        fn id_num['t](x: 't) -> 't where Int['t] { x }
    "#;

    let (module_path, result, tcx) =
        typecheck_src("typechecks_generic_id_with_class_constraint", src);
    assert_typechecks("typechecks_generic_id_with_class_constraint", &result);
    let ty_var = TyVar::new("?s0");
    let vars = vec![ty_var.clone()];
    let body = Ty::Var(ty_var.clone());
    let expected_ty = Ty::func(vec![body.clone()], body.clone());
    let trait_name = module_path.append("Int").to_string();
    let expected_preds = vec![Predicate::class(trait_name, vec![body])];
    assert_scheme_eq(
        &tcx,
        &module_path,
        "id_num",
        &vars,
        expected_ty,
        &expected_preds,
    );
}

#[test]
fn typechecks_u32_literal_function() {
    let src = r#"
        fn lit() -> u32 { 1u32 }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_u32_literal_function", src);
    assert_typechecks("typechecks_u32_literal_function", &result);
    let expected_ty = Ty::func(vec![], Ty::u32());
    assert_scheme_eq(&tcx, &module_path, "lit", &[], expected_ty, &[]);
}

#[test]
fn typechecks_generic_plain_id_function() {
    let src = r#"
        fn id_generic['t](x: 't) -> 't { x }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_generic_plain_id_function", src);
    assert_typechecks("typechecks_generic_plain_id_function", &result);
    let var = TyVar::new("?s0");
    let vars = vec![var.clone()];
    let body = Ty::Var(var);
    let expected_ty = Ty::func(vec![body.clone()], body);
    assert_scheme_eq(&tcx, &module_path, "id_generic", &vars, expected_ty, &[]);
}

#[test]
fn typechecks_pair_function() {
    let src = r#"
        fn pair(x: u32, y: bool) -> (u32, bool) { (x, y) }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_pair_function", src);
    assert_typechecks("typechecks_pair_function", &result);
    let expected_ty = Ty::func(
        vec![Ty::u32(), Ty::bool()],
        Ty::tuple(vec![Ty::u32(), Ty::bool()]),
    );
    assert_scheme_eq(&tcx, &module_path, "pair", &[], expected_ty, &[]);
}

#[test]
fn typechecks_f64_literal_function() {
    let src = r#"
        fn lit_f64() -> f64 { 1.0f64 }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_f64_literal_function", src);
    assert_typechecks("typechecks_f64_literal_function", &result);
    let expected_ty = Ty::func(vec![], Ty::f64());
    assert_scheme_eq(&tcx, &module_path, "lit_f64", &[], expected_ty, &[]);
}

#[test]
fn typechecks_local_closure_call() {
    let src = r#"
        fn call_local_closure() -> u32 {
            identity = (value) => value
            identity(41u32)
        }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_local_closure_call", src);
    assert_typechecks("typechecks_local_closure_call", &result);
    let expected_ty = Ty::func(vec![], Ty::u32());
    assert_scheme_eq(
        &tcx,
        &module_path,
        "call_local_closure",
        &[],
        expected_ty,
        &[],
    );
}

#[test]
fn typechecks_closure_with_capture() {
    let src = r#"
        fn call_closure_with_capture(base: u32) -> u32 {
            capture_base = (value) => base
            capture_base(1u32)
        }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_closure_with_capture", src);
    assert_typechecks("typechecks_closure_with_capture", &result);
    let expected_ty = Ty::func(vec![Ty::u32()], Ty::u32());
    assert_scheme_eq(
        &tcx,
        &module_path,
        "call_closure_with_capture",
        &[],
        expected_ty,
        &[],
    );
}

#[test]
fn typechecks_bool_literal_function() {
    let src = r#"
        fn lit_bool() -> bool { true }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_bool_literal_function", src);
    assert_typechecks("typechecks_bool_literal_function", &result);
    let expected_ty = Ty::func(vec![], Ty::bool());
    assert_scheme_eq(&tcx, &module_path, "lit_bool", &[], expected_ty, &[]);
}

#[test]
fn typechecks_generic_swap_function() {
    let src = r#"
        fn swap['a, 'b](x: 'a, y: 'b) -> ('b, 'a) { (y, x) }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_generic_swap_function", src);
    assert_typechecks("typechecks_generic_swap_function", &result);
    let var_a = TyVar::new("?s0");
    let var_b = TyVar::new("?s1");
    let vars = vec![var_a.clone(), var_b.clone()];
    let ty_a = Ty::Var(var_a);
    let ty_b = Ty::Var(var_b);
    let expected_ty = Ty::func(
        vec![ty_a.clone(), ty_b.clone()],
        Ty::tuple(vec![ty_b, ty_a]),
    );
    assert_scheme_eq(&tcx, &module_path, "swap", &vars, expected_ty, &[]);
}

#[test]
fn typechecks_nil_literal_function() {
    let src = r#"
        fn lit_nil() -> nilable[u32] { nil }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_nil_literal_function", src);
    assert_typechecks("typechecks_nil_literal_function", &result);
    let expected_ty = Ty::func(vec![], Ty::nilable(Ty::u32()));
    assert_scheme_eq(&tcx, &module_path, "lit_nil", &[], expected_ty, &[]);
}

#[test]
fn typechecks_some_literal_function() {
    let src = r#"
        fn lit_some() -> nilable[u32] { some(1u32) }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_some_literal_function", src);
    assert_typechecks("typechecks_some_literal_function", &result);
    let expected_ty = Ty::func(vec![], Ty::nilable(Ty::u32()));
    assert_scheme_eq(&tcx, &module_path, "lit_some", &[], expected_ty, &[]);
}

#[test]
fn typechecks_if_bool_expression() {
    let src = r#"
        fn if_bool(b: bool) -> bool {
            if b { true } else { false }
        }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_if_bool_expression", src);
    assert_typechecks("typechecks_if_bool_expression", &result);
    let expected_ty = Ty::func(vec![Ty::bool()], Ty::bool());
    assert_scheme_eq(&tcx, &module_path, "if_bool", &[], expected_ty, &[]);
}

#[test]
fn typechecks_while_unit_expression() {
    let src = r#"
        fn while_unit(b: bool) -> () {
            while b { () }
        }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_while_unit_expression", src);
    assert_typechecks("typechecks_while_unit_expression", &result);
    let expected_ty = Ty::func(vec![Ty::bool()], Ty::unit());
    assert_scheme_eq(&tcx, &module_path, "while_unit", &[], expected_ty, &[]);
}

#[test]
fn typechecks_loop_with_break_bool() {
    let src = r#"
        fn loop_break(b: bool) -> bool {
            loop { break b; }
        }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_loop_with_break_bool", src);
    assert_typechecks("typechecks_loop_with_break_bool", &result);
    let expected_ty = Ty::func(vec![Ty::bool()], Ty::bool());
    assert_scheme_eq(&tcx, &module_path, "loop_break", &[], expected_ty, &[]);
}

#[test]
fn typechecks_if_pattern_nilable_expression() {
    let src = r#"
        fn pattern_if(arg: nilable[u32]) -> u32 {
            if some(x) = arg { x } else { 0u32 }
        }
    "#;

    let (module_path, result, tcx) = typecheck_src("typechecks_if_pattern_nilable_expression", src);
    assert_typechecks("typechecks_if_pattern_nilable_expression", &result);
    let expected_ty = Ty::func(vec![Ty::nilable(Ty::u32())], Ty::u32());
    assert_scheme_eq(&tcx, &module_path, "pattern_if", &[], expected_ty, &[]);
}

#[test]
fn typechecks_struct_literal_and_field_access() {
    let src = r#"
        struct Pair { x: u32, y: bool }

        fn mk_pair(x: u32, y: bool) -> Pair {
            Pair { x, y }
        }

        fn project_x(p: Pair) -> u32 {
            p.x
        }
    "#;

    let (module_path, result, tcx) =
        typecheck_src("typechecks_struct_literal_and_field_access", src);
    assert_typechecks("typechecks_struct_literal_and_field_access", &result);

    let pair_path = module_path.append("Pair");
    let pair_ty = Ty::Const(pair_path);

    let mk_pair_ty = Ty::func(vec![Ty::u32(), Ty::bool()], pair_ty.clone());
    assert_scheme_eq(&tcx, &module_path, "mk_pair", &[], mk_pair_ty, &[]);

    let project_ty = Ty::func(vec![pair_ty], Ty::u32());
    assert_scheme_eq(&tcx, &module_path, "project_x", &[], project_ty, &[]);
}

#[test]
fn typechecks_list_and_int_literals() {
    let src = r#"
        trait Int['a] {
            default(int)
        }

        impl Int[int] {}
        impl Int[uint] {}

        struct list['a] {
            values: rawptr['a]
            len: uint
            capacity: uint
        }

        fn main() {
            l = [1,2]
        }
    "#;

    let (module_path, result, tcx, bindings) = typecheck_src_with_bindings("test", src);
    assert_typechecks("typechecks_list_and_int_literals", &result);

    assert_local_scheme_eq(
        &tcx,
        &bindings,
        &module_path,
        "main::l",
        &[],
        Ty::proj("test::list", vec![Ty::int()]),
        &[],
    );
}

#[test]
fn typechecks_pointer_field_access_unconstrained_ptr_add() {
    let src = r#"
@intrinsic extern fn __rawptr_add(p: rawptr['a], offset: uint) -> rawptr['a]
@intrinsic extern fn u32_add(lhs: uint, rhs: uint) -> uint

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

impl Add[rawptr['a], uint, rawptr['a]] {
    fn +(lhs: rawptr['a], rhs: uint) -> rawptr['a] => __rawptr_add(lhs, rhs)
}

impl Add[uint, uint, uint] {
    fn +(lhs: uint, rhs: uint) -> uint => u32_add(lhs, rhs)
}

struct list['a] {
    values: rawptr['a]
    len: uint
    capacity: uint
}

fn set_like(self: *list['a], idx: uint, el: 'a) -> 'a? {
    ptr = self.values + idx
    nil
}
"#;

    let (_, result, _) =
        typecheck_src("typechecks_pointer_field_access_unconstrained_ptr_add", src);
    assert_typechecks(
        "typechecks_pointer_field_access_unconstrained_ptr_add",
        &result,
    );
}

#[test]
fn typechecks_index_operator_returns_nilable_elem() {
    let src = r#"
trait Int['a] {
    default(int)
}

impl Int[int] {}
impl Int[uint] {}

trait Index['a, 'el, 'idx] {
    fn get(self: *'a, idx: 'idx) -> 'el?
    fn set(self: *'a, idx: 'idx, el: 'el) -> 'el?
}

struct list['a] {
    values: rawptr['a]
    len: uint
    capacity: uint
}

impl Index[list['a], 'a, uint] {
    fn get(self: *list['a], idx: uint) -> 'a? { nil }
    fn set(self: *list['a], idx: uint, el: 'a) -> 'a? { nil }
}

fn main() {
    l = [1, 2]
    curr = l[1]
}
"#;

    let (module_path, result, tcx, bindings) =
        typecheck_src_with_bindings("typechecks_index_operator_returns_nilable_elem", src);
    assert_typechecks("typechecks_index_operator_returns_nilable_elem", &result);

    assert_local_scheme_eq(
        &tcx,
        &bindings,
        &module_path,
        "main::curr",
        &[],
        Ty::nilable(Ty::int()),
        &[],
    );
}

#[test]
fn typechecks_index_assignment() {
    let src = r#"
trait Int['a] {
    default(int)
}

impl Int[int] {}
impl Int[uint] {}

trait Index['a, 'el, 'idx] {
    fn get(self: *'a, idx: 'idx) -> 'el?
    fn set(self: *'a, idx: 'idx, el: 'el) -> 'el?
}

struct list['a] {
    values: rawptr['a]
    len: uint
    capacity: uint
}

impl Index[list['a], 'a, uint] {
    fn get(self: *list['a], idx: uint) -> 'a? { nil }
    fn set(self: *list['a], idx: uint, el: 'a) -> 'a? { nil }
}

fn main() {
    l = [1, 2]
    l[1] = 10
}
"#;

    let (_, result, _) = typecheck_src("typechecks_index_assignment", src);
    assert_typechecks("typechecks_index_assignment", &result);
}

#[test]
fn typechecks_polymorphic_closure() {
    let src = r#"
@intrinsic extern fn u32_add(a: u32, b: u32) -> u32
@intrinsic extern fn i8_add(a: i8, b: i8) -> i8

trait Int['a] {}
impl Int[u32] {}
impl Int[i8] {}

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

impl Add[u32, u32, u32] {
    fn +(lhs: u32, rhs: u32) -> u32 => u32_add(lhs, rhs)
}

impl Add[i8, i8, i8] {
    fn +(lhs: i8, rhs: i8) -> i8 => i8_add(lhs, rhs)
}

fn poly() {
   add_one = (a) => a + 1
   a = add_one(3u32)
   b = add_one(10i8)
}
"#;

    let (module_path, result, tcx, bindings) =
        typecheck_src_with_bindings("typechecks_polymorphic_closure", src);
    assert_typechecks("typechecks_polymorphic_closure", &result);

    // check the type of add_one
    let var_a = TyVar::new("?s0");
    let var_b = TyVar::new("?s1");
    let var_c = TyVar::new("?s2");
    let vars = vec![var_a.clone(), var_b.clone(), var_c.clone()];
    let ty_a = Ty::Var(var_a);
    let ty_b = Ty::Var(var_b);
    let ty_c = Ty::Var(var_c);
    let expected_ty = Ty::func(vec![ty_b.clone()], ty_c.clone());
    let add_trait = module_path.append("Add").to_string();
    let int_trait = module_path.append("Int").to_string();
    let expected_predicates = vec![
        Predicate::class(int_trait, vec![ty_a.clone()]),
        Predicate::class(add_trait, vec![ty_b, ty_a, ty_c]),
    ];
    assert_local_scheme_eq(
        &tcx,
        &bindings,
        &module_path,
        "poly::add_one",
        &vars,
        expected_ty,
        &expected_predicates,
    );

    // check the type of `a`
    assert_local_ty_eq(&tcx, &bindings, &module_path, "poly::a", Ty::u32());

    // check the type of `b`
    assert_local_ty_eq(&tcx, &bindings, &module_path, "poly::b", Ty::i8());
}

#[test]
fn typechecks_polymorphic_calls() {
    let src = r#"
fn callee(x: 'a) -> 'a {
    x
}

fn caller(y: 'a) -> 'a {
    callee(y)
}    
"#;

    let (module_path, result, tcx, _) =
        typecheck_src_with_bindings("typechecks_polymorphic_calls", src);
    assert_typechecks("typechecks_polymorphic_calls", &result);

    let var_a = TyVar::new("?s0");
    let ty_a = Ty::Var(var_a.clone());
    let caller_ty = Ty::func(vec![ty_a.clone()], ty_a.clone());

    assert_scheme_eq(&tcx, &module_path, "caller", &[var_a], caller_ty, &[]);

    let var_a = TyVar::new("?s0");
    let ty_a = Ty::Var(var_a.clone());
    let callee_ty = Ty::func(vec![ty_a.clone()], ty_a.clone());

    assert_scheme_eq(&tcx, &module_path, "callee", &[var_a], callee_ty, &[]);
}

#[test]
fn typechecks_function_with_qualifiers() {
    let src = r#"
trait Int['a] {}
trait Lt['a, 'b] {
    fn <(lhs: 'a, rhs: 'b) -> bool
}
trait Neg['a, 'b] {
    fn -(lhs: 'a) -> 'b
}

fn abs(a: 'a) -> 'a where Int['a], Lt['a, 'a], Neg['a, 'a] {
    if a < 0 {
        -a
    } else {
        a
    }
}
"#;

    let (module_path, result, tcx, _) =
        typecheck_src_with_bindings("typechecks_function_with_qualifiers", src);
    assert_typechecks("typechecks_function_with_qualifiers", &result);

    let var_a = TyVar::new("?s0");
    let ty_a = Ty::Var(var_a.clone());
    let abs_ty = Ty::func(vec![ty_a.clone()], ty_a.clone());
    let int_trait = module_path.append("Int").to_string();
    let lt_trait = module_path.append("Lt").to_string();
    let neg_trait = module_path.append("Neg").to_string();
    let predicates = vec![
        Predicate::class(int_trait, vec![ty_a.clone()]),
        Predicate::class(lt_trait, vec![ty_a.clone(), ty_a.clone()]),
        Predicate::class(neg_trait, vec![ty_a.clone(), ty_a.clone()]),
    ];
    assert_scheme_eq(&tcx, &module_path, "abs", &[var_a], abs_ty, &predicates);
}

#[test]
fn typechecks_method_call_discharged_by_given_trait() {
    let src = r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

fn io_print(v: 'a) -> () where ToStr['a] {
    s = v.to_str()
    _ = s
}
"#;

    let (module_path, result, tcx, bindings) =
        typecheck_src_with_bindings("typechecks_method_call_discharged_by_given_trait", src);
    assert_typechecks("typechecks_method_call_discharged_by_given_trait", &result);
    assert_local_ty_eq(&tcx, &bindings, &module_path, "io_print::s", Ty::string());
}

#[test]
fn typechecks_cross_function_given_trait_discharge() {
    let src = r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

fn io_print(v: 'a) -> () where ToStr['a] {
    s = v.to_str()
    _ = s
}

fn core_print(v: 'a) -> () where ToStr['a] {
    io_print(v)
}
"#;

    let (_module_path, result, _tcx) =
        typecheck_src("typechecks_cross_function_given_trait_discharge", src);
    assert_typechecks("typechecks_cross_function_given_trait_discharge", &result);
}

#[test]
fn typechecks_signed_tostr_calls_abs_under_qualifiers() {
    let src = r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

trait Int['a] {
    default(int)
}

trait Lt['a, 'b] {
    fn <(lhs: 'a, rhs: 'b) -> bool
}

trait Neg['a, 'b] {
    fn -(lhs: 'a) -> 'b
}

trait SignedInt['a] {}

impl Int[int] {}
impl SignedInt[int] {}

impl Lt[int, int] {
    fn <(lhs: int, rhs: int) -> bool { true }
}

impl Neg[int, int] {
    fn -(lhs: int) -> int { lhs }
}

fn abs(a: 'a) -> 'a where Int['a], Lt['a, 'a], Neg['a, 'a] {
    a
}

impl ToStr['a] where SignedInt['a], Int['a], Lt['a, 'a], Neg['a, 'a] {
    fn to_str(self: 'a) -> string {
        i = abs(self)
        _ = i
        ""
    }
}

fn core_print(v: 'a) -> () where ToStr['a] {
    s = v.to_str()
    _ = s
}
"#;

    let (_module_path, result, _tcx) =
        typecheck_src("typechecks_signed_tostr_calls_abs_under_qualifiers", src);
    assert_typechecks(
        "typechecks_signed_tostr_calls_abs_under_qualifiers",
        &result,
    );
}

#[test]
fn typechecks_generic_tostr_for_u32() {
    let src = r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

trait Int['a] {}
trait UnsignedInt['a] {}
trait Div['a, 'b, 'c] {}
trait Mod['a, 'b, 'c] {}
trait Eq['a, 'b] {}

impl Int[u32] {}
impl UnsignedInt[u32] {}
impl Div[u32, u32, u32] {}
impl Mod[u32, u32, u32] {}
impl Eq[u32, u32] {}

impl ToStr['a] where UnsignedInt['a], Int['a], Div['a, 'a, 'a], Mod['a, 'a, 'a], Eq['a, 'a] {
    fn to_str(self: 'a) -> string {
        ""
    }
}

fn print(v: 'a) -> () where ToStr['a] {
    s = v.to_str()
    _ = s
}

fn f(x: u32) -> () {
    print(x)
}
"#;

    let (_module_path, result, _tcx) = typecheck_src("typechecks_generic_tostr_for_u32", src);
    assert_typechecks("typechecks_generic_tostr_for_u32", &result);
}

#[test]
fn typechecks_writev_stdout_wasi_shape() {
    let src = r#"
@intrinsic extern fn int_add(lhs: int, rhs: int) -> int
@intrinsic extern fn uint_add(lhs: uint, rhs: uint) -> uint
@intrinsic extern fn uint_lt(lhs: uint, rhs: uint) -> bool
@intrinsic extern fn __deref_raw(p: rawptr['a]) -> 'a
@intrinsic extern fn __rawptr_add(p: rawptr['a], offset: uint) -> rawptr['a]

trait Int['a] {
    default(int)
}

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

trait Lt['a, 'b] {
    fn <(lhs: 'a, rhs: 'b) -> bool
}

trait Deref['a, 'b] {
    fn deref(self: 'a) -> 'b
}

impl Int[int] {}
impl Int[uint] {}

impl Add[int, int, int] {
    fn +(lhs: int, rhs: int) -> int => int_add(lhs, rhs)
}

impl Add[uint, uint, uint] {
    fn +(lhs: uint, rhs: uint) -> uint => uint_add(lhs, rhs)
}

impl Add[rawptr['a], uint, rawptr['a]] {
    fn +(lhs: rawptr['a], rhs: uint) -> rawptr['a] => __rawptr_add(lhs, rhs)
}

impl Lt[uint, uint] {
    fn <(lhs: uint, rhs: uint) -> bool => uint_lt(lhs, rhs)
}

impl Deref[rawptr['a], 'a] {
    fn deref(self: rawptr['a]) -> 'a => __deref_raw(self)
}

extern wasi fn fd_write(fd: int, iov: *IOVec, iov_len: uint, nwritten: *uint) -> uint

struct string {
    raw_ptr: rawptr[u8]
    len: uint
}

struct IOVec {
    base: rawptr[u8]
    len: uint
}

fn writev_stdout(chunks: *string, n: uint) -> uint {
    iovecs = new(IOVec, n)
    raw_chunks = chunks as rawptr[string]
    raw_iovecs = iovecs as rawptr[IOVec]
    mut i = 0
    while i < n {
        raw_chunk = *(raw_chunks + i)
        chunk = raw_chunk as string
        ptr = raw_iovecs + i
        *ptr = IOVec { base: chunk.raw_ptr, len: chunk.len }
        i += 1
    }

    wrote = 0
    _ = fd_write(1, iovecs, n, &wrote)
    wrote
}

fn main() {
    chunks = new(string, 2)
    _ = writev_stdout(chunks, 2)
}
"#;

    let (_module_path, result, _tcx) = typecheck_src("core", src);
    assert_typechecks("typechecks_writev_stdout_wasi_shape", &result);
}

#[test]
fn typechecks_function_with_int_literals() {
    let src = r#"
trait Int['a] {
    default(int)
}
impl Int[int] {}
impl Int[uint] {}

fn main() {
    a = 10
    b = 20
}
"#;

    let (module_path, result, tcx, _) = typecheck_src_with_bindings("test", src);
    assert_typechecks("test", &result);
    let a_path = module_path.append_path("main::a");
    let scheme = tcx.all_schemes().get(&a_path).expect("a scheme");
    assert!(scheme.vars.is_empty(), "scheme vars not empty: {}", scheme);
    assert_eq!(*scheme.mono(), Ty::int());
}

#[test]
fn typechecks_function_with_literals_and_string_struct() {
    let src = r#"
extern fn malloc(size: uint) -> rawptr[u8]

trait Int['a] {
    default(int)
}
impl Int[int] {}
impl Int[uint] {}

struct string {
    raw_ptr: rawptr[u8]
    len: uint
}

fn mk_string() -> string {
    len = 10
    raw_ptr = malloc(len)
    string { raw_ptr, len }
}
"#;

    let (_module_path, result, _tcx, _) = typecheck_src_with_bindings("test", src);
    assert_typechecks("test", &result);
}

#[test]
fn typechecks_function_with_literals_and_rawptr() {
    let src = r#"
extern fn malloc(size: uint) -> rawptr[u8]

trait Int['a] {
    default(int)
}
impl Int[int] {}
impl Int[uint] {}

fn mk_string() {
    len = 10
    raw_ptr = malloc(len)
}
"#;

    let (module_path, result, tcx, _) = typecheck_src_with_bindings("test", src);
    assert_typechecks("test", &result);
    let len_path = module_path.append_path("mk_string::len");
    let scheme = tcx.all_schemes().get(&len_path).expect("len scheme");
    assert!(scheme.vars.is_empty(), "scheme vars not empty: {}", scheme);
    assert_eq!(*scheme.mono(), Ty::uint());
}

#[test]
fn typechecks_int_literal_not_captured_by_givens() {
    let src = r#"
extern fn malloc(size: uint) -> rawptr[u8]

trait Int['a] {
    default(int)
}
impl Int[int] {}
impl Int[uint] {}

fn foo['a](x: 'a) -> rawptr[u8] where Int['a] {
    len = 1
    _ = x
    malloc(len)
}
"#;

    let (module_path, result, tcx, bindings) =
        typecheck_src_with_bindings("typechecks_int_literal_not_captured_by_givens", src);
    assert_typechecks("typechecks_int_literal_not_captured_by_givens", &result);
    assert_local_ty_eq(&tcx, &bindings, &module_path, "foo::len", Ty::uint());
}

#[test]
fn typechecks_generic_div_assign_uses_receiver_given_to_constrain_rhs() {
    let src = r#"
trait Int['a] {
    default(int)
}

trait Div['a, 'b, 'c] {
    fn /(lhs: 'a, rhs: 'b) -> 'c
}

impl Int[int] {}
impl Int[uint] {}

impl Div[int, int, int] {
    fn /(lhs: int, rhs: int) -> int { lhs }
}

fn foo(i: 'a) -> 'a where Int['a], Div['a, 'a, 'a] {
    i /= 10
    i
}
"#;

    let (_module_path, result, _tcx) = typecheck_src(
        "typechecks_generic_div_assign_uses_receiver_given_to_constrain_rhs",
        src,
    );
    assert_typechecks(
        "typechecks_generic_div_assign_uses_receiver_given_to_constrain_rhs",
        &result,
    );
}

#[test]
fn typechecks_generic_eq_zero_uses_receiver_given_to_constrain_rhs() {
    let src = r#"
trait Int['a] {
    default(int)
}

trait Eq['a, 'b] {
    fn ==(lhs: 'a, rhs: 'b) -> bool
}

impl Int[int] {}
impl Int[uint] {}

impl Eq[int, int] {
    fn ==(lhs: int, rhs: int) -> bool { true }
}

fn is_one(x: 'a) -> bool where Int['a], Eq['a, 'a] {
    x == 1
}
"#;

    let (_module_path, result, _tcx) = typecheck_src(
        "typechecks_generic_eq_zero_uses_receiver_given_to_constrain_rhs",
        src,
    );
    assert_typechecks(
        "typechecks_generic_eq_zero_uses_receiver_given_to_constrain_rhs",
        &result,
    );
}

#[test]
fn typechecks_rawptr_deref_assignment() {
    let src = r#"
extern fn malloc(size: uint) -> rawptr[u8]
@intrinsic extern fn __deref_raw(p: rawptr['a]) -> 'a
@intrinsic extern fn __deref_ptr(p: *'a) -> 'a

trait Int['a] {
    default(int)
}
impl Int[int] {}
impl Int[uint] {}

trait Deref['a, 'b] {
    fn deref(self: 'a) -> 'b
}

impl Deref[rawptr['a], 'a] {
    fn deref(self: rawptr['a]) -> 'a => __deref_raw(self)
}

fn main() {
    ptr = malloc(1)
    *ptr = ('0' as u8)
}
"#;

    let (_module_path, result, _tcx, _) = typecheck_src_with_bindings("test", src);
    assert_typechecks("test", &result);
}

#[test]
fn typechecks_rawptr_add_and_deref_assignment() {
    let src = r#"
@intrinsic extern fn __deref_raw(p: rawptr['a]) -> 'a
@intrinsic extern fn __deref_ptr(p: *'a) -> 'a
@intrinsic extern fn __rawptr_add(p: rawptr['a], offset: uint) -> rawptr['a]
@intrinsic extern fn int_add(lhs: int, rhs: int) -> int
@intrinsic extern fn uint_add(lhs: uint, rhs: uint) -> uint

extern fn mk_string() -> string

trait Int['a] {
    default(int)
}

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

trait Deref['a, 'b] {
    fn deref(self: 'a) -> 'b
}

impl Int[int] {}
impl Int[uint] {}

impl Add[int, int, int] {
    fn +(lhs: int, rhs: int) -> int => int_add(lhs, rhs)
}

impl Add[uint, uint, uint] {
    fn +(lhs: uint, rhs: uint) -> uint => uint_add(lhs, rhs)
}

impl Add[rawptr['a], uint, rawptr['a]] {
    fn +(lhs: rawptr['a], rhs: uint) -> rawptr['a] => __rawptr_add(lhs, rhs)
}

impl Deref[rawptr['a], 'a] {
    fn deref(self: rawptr['a]) -> 'a => __deref_raw(self)
}

impl Deref[*'a, 'a] {
    fn deref(self: *'a) -> 'a => __deref_ptr(self)
}

fn main() {
    s = mk_string()
    nl = "\n"
    chunks = new(string, 2)
    mut ptr = chunks as rawptr[string]
    *ptr = s
    ptr = ptr + 1
    *ptr = nl
}
"#;

    let (_module_path, result, _tcx, _) = typecheck_src_with_bindings("test", src);
    assert_typechecks("test", &result);
}

#[test]
fn typechecks_method_call_via_dot_callee() {
    let src = r#"
	trait Foo['a] {
	    fn bar(self: 'a) -> ()
}

impl Foo[bool] {
    fn bar(self: bool) -> () => ()
}

fn main() {
    v = true
    _ = v.bar()
}
"#;

    let (_module_path, result, _tcx, _) = typecheck_src_with_bindings("test", src);
    assert_typechecks("test", &result);
}

#[test]
fn typechecks_function_with_literals_and_add() {
    let src = r#"
@intrinsic extern fn int_add(lhs: int, rhs: int) -> int
@intrinsic extern fn uint_add(lhs: uint, rhs: uint) -> uint

trait Int['a] {
    default(int)
}

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

impl Int[int] {}
impl Int[uint] {}

impl Add[int, int, int] {
    fn +(lhs: int, rhs: int) -> int => int_add(lhs, rhs)
}

impl Add[uint, uint, uint] {
    fn +(lhs: uint, rhs: uint) -> uint => uint_add(lhs, rhs)
}

fn foo(x: uint) {}

fn main() {
    len = 10
    len += 1
    foo(len)
}
"#;

    let (_module_path, result, _tcx, _) = typecheck_src_with_bindings("test", src);
    assert_typechecks("test", &result);
}

#[test]
fn typechecks_impl_function() {
    let src = r#"
@intrinsic extern fn int_add(lhs: int, rhs: int) -> int
@intrinsic extern fn int_div(lhs: int, rhs: int) -> int
@intrinsic extern fn int_eq(lhs: int, rhs: int) -> bool
@intrinsic extern fn int_lt(lhs: int, rhs: int) -> bool

trait Int['a] {
    default(int)
}

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

trait Div['a, 'b, 'c] {
    fn /(lhs: 'a, rhs: 'b) -> 'c
}

trait Eq['a, 'b] {
    fn ==(lhs: 'a, rhs: 'b) -> bool
}

trait Lt['a, 'b] {
    fn <(lhs: 'a, rhs: 'b) -> bool
}

trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

impl Int[int] {}

impl Add[int, int, int] {
    fn +(lhs: int, rhs: int) -> int => int_add(lhs, rhs)
}

impl Div[int, int, int] {
    fn /(lhs: int, rhs: int) -> int => int_div(lhs, rhs)
}

impl Eq[int, int] {
    fn ==(lhs: int, rhs: int) -> bool => int_eq(lhs, rhs)
}

impl Lt[int, int] {
    fn <(lhs: int, rhs: int) -> bool => int_lt(lhs, rhs)
}

impl ToStr[int] {
    fn to_str(self: int) -> string {
        len = 1
        mut i = self
        while true {
            i /= 10
            len += 1
            if i == 0 {
                break
            }
        }

        if self < 0 {
            len += 1
        }

        "int"
    }
}

fn main() {
    a = 10
    s = a.to_str()
}
"#;

    let (_module_path, result, _tcx, _) = typecheck_src_with_bindings("test", src);
    assert_typechecks("test", &result);
}

#[test]
fn typechecks_impl_method_infers_return_and_omits_self_type() {
    let src = r#"
struct string {}

trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

struct A {}

impl ToStr[A] {
    fn to_str(self) => string {}
}

fn main() {
    a = A {}
    _ = a.to_str()
}
"#;

    let (_module_path, result, _tcx, _) = typecheck_src_with_bindings("test", src);
    assert_typechecks("test", &result);
}

// Regression test for io.ray:14 failure - rawptr addition with integer literal
// in a function with trait constraints, calling a function that does rawptr arithmetic.
#[test]
fn typechecks_rawptr_add_with_integer_literal_in_constrained_function() {
    let src = r#"
@intrinsic extern fn __deref_raw(p: rawptr['a]) -> 'a
@intrinsic extern fn __rawptr_add(p: rawptr['a], offset: uint) -> rawptr['a]
@intrinsic extern fn uint_add(lhs: uint, rhs: uint) -> uint

trait Int['a] {
    default(int)
}

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

trait Deref['a, 'b] {
    fn deref(self: 'a) -> 'b
}

trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

trait Lt['a, 'b] {
    fn <(lhs: 'a, rhs: 'b) -> bool
}

impl Int[int] {}
impl Int[uint] {}

impl Add[uint, uint, uint] {
    fn +(lhs: uint, rhs: uint) -> uint => uint_add(lhs, rhs)
}

@intrinsic extern fn uint_lt(lhs: uint, rhs: uint) -> bool
impl Lt[uint, uint] {
    fn <(lhs: uint, rhs: uint) -> bool => uint_lt(lhs, rhs)
}

struct string {
    raw_ptr: rawptr[u8]
    len: uint
}

impl Add[rawptr['a], uint, rawptr['a]] {
    fn +(lhs: rawptr['a], rhs: uint) -> rawptr['a] => __rawptr_add(lhs, rhs)
}

impl Deref[rawptr['a], 'a] {
    fn deref(self: rawptr['a]) -> 'a => __deref_raw(self)
}

struct Chunk {
    data: rawptr[u8]
    len: uint
}

fn write_chunks(chunks: *Chunk, n: uint) -> uint {
    raw_chunks = chunks as rawptr[Chunk]
    mut i = 0
    while i < n {
        ptr = raw_chunks + i
        _ = *ptr
        i += 1
    }
    n
}

fn print(v: 'a) -> () where ToStr['a] {
    s = v.to_str()
    chunks = new(Chunk, 2)
    mut ptr = chunks as rawptr[Chunk]
    *ptr = Chunk { data: s.raw_ptr, len: s.len }
    ptr = ptr + 1
    *ptr = Chunk { data: s.raw_ptr, len: s.len }
    _ = write_chunks(chunks, 2)
}
"#;

    let (_module_path, result, _tcx, _) = typecheck_src_with_bindings("test", src);
    assert_typechecks("test", &result);
}

#[test]
fn typechecks_field_access_on_pointer_to_generic_struct() {
    let src = r#"
@intrinsic extern fn __deref_raw(p: rawptr['a]) -> 'a
@intrinsic extern fn __rawptr_add(p: rawptr['a], offset: uint) -> rawptr['a]
@intrinsic extern fn uint_add(lhs: uint, rhs: uint) -> uint

trait Int['a] {
    default(int)
}

trait Add['a, 'b, 'c] {
    fn +(lhs: 'a, rhs: 'b) -> 'c
}

trait Deref['a, 'b] {
    fn deref(self: 'a) -> 'b
}

trait GtEq['a, 'b] {
    fn >=(lhs: 'a, rhs: 'b) -> bool
}

trait Index['container, 'element, 'index] {
    fn get(self: *'container, idx: 'index) -> 'element?
    fn set(self: *'container, idx: 'index, el: 'element) -> 'element?
}

impl Int[int] {}
impl Int[uint] {}

impl Add[uint, uint, uint] {
    fn +(lhs: uint, rhs: uint) -> uint => uint_add(lhs, rhs)
}

impl Add[rawptr['a], uint, rawptr['a]] {
    fn +(lhs: rawptr['a], rhs: uint) -> rawptr['a] => __rawptr_add(lhs, rhs)
}

impl Deref[rawptr['a], 'a] {
    fn deref(self: rawptr['a]) -> 'a => __deref_raw(self)
}

@intrinsic extern fn uint_gteq(lhs: uint, rhs: uint) -> bool
impl GtEq[uint, uint] {
    fn >=(lhs: uint, rhs: uint) -> bool => uint_gteq(lhs, rhs)
}

struct Container['a] {
    values: rawptr['a]
    len: uint
}

impl Index[Container['a], 'a, uint] {
    fn get(self: *Container['a], idx: uint) -> 'a? {
        if idx >= self.len {
            return nil
        }
        ptr = self.values + idx
        some(*ptr)
    }

    fn set(self: *Container['a], idx: uint, el: 'a) -> 'a? {
        nil
    }
}
"#;

    let (_module_path, result, _tcx, _) = typecheck_src_with_bindings("test", src);
    assert_typechecks("test", &result);
}

#[test]
fn typechecks_scoped_static_call_in_impl_with_bounds() {
    let src = r#"
        struct A['a, 'b] {}
        struct B['a, 'b] { value: A['a, 'b] }

        trait T['a] {}
        trait U['a] { fn go(self: *'a) -> u32 }

        impl U[B['a, 'b]] where T['a] {
            fn go(self: *B['a, 'b]) -> u32 {
                A['a, 'b]::check()
            }
        }

        impl object A['a, 'b] where T['a] {
            static fn check() -> u32 { 0u32 }
        }
    "#;

    let (_module_path, result, _tcx) =
        typecheck_src("typechecks_scoped_static_call_in_impl_with_bounds", src);
    assert_typechecks("typechecks_scoped_static_call_in_impl_with_bounds", &result);
}

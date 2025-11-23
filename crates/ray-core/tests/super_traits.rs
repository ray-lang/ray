#![cfg(test)]

use ray_typing::ty::{Ty, TyVar};
use ray_shared::pathlib::Path;
use ray_typing::top::types::{Class, ClassEnv, Predicate};

fn ty_var(name: &str) -> Ty {
    Ty::var(Path::from(name))
}

#[test]
fn supertraits_instantiate_mapped_arguments() {
    let self_param = ty_var("test::Map::Self");
    let key_param = ty_var("test::Map::K");
    let val_param = ty_var("test::Map::V");

    let super_template = vec![Ty::Tuple(vec![key_param.clone(), val_param.clone()])];
    let class = Class::new(
        vec![self_param.clone(), key_param.clone(), val_param.clone()],
        vec![("test::Iterable".to_string(), super_template)],
        vec![],
    );

    let mut env = ClassEnv::<Ty, TyVar>::new();
    env.add_class("test::Map".to_string(), class);

    let key_ty = Ty::con("int");
    let val_ty = Ty::con("uint");
    let map_ty = Ty::Projection(
        Box::new(Ty::con("test::Map")),
        vec![key_ty.clone(), val_ty.clone()],
    );

    let predicate = Predicate::class(
        "test::Map".to_string(),
        map_ty,
        vec![key_ty.clone(), val_ty.clone()],
    );
    let supers = env.by_superclass(&predicate);

    let expected = Predicate::class(
        "test::Iterable".to_string(),
        Ty::Tuple(vec![key_ty, val_ty]),
        vec![],
    );

    assert!(
        supers.contains(&expected),
        "expected {:?} to contain {:?}",
        supers,
        expected
    );
}

#[test]
fn supertraits_support_reordered_arguments() {
    let self_param = ty_var("test::Pair::Self");
    let a_param = ty_var("test::Pair::A");
    let b_param = ty_var("test::Pair::B");

    let super_template = vec![Ty::Tuple(vec![b_param.clone(), a_param.clone()])];
    let class = Class::new(
        vec![self_param.clone(), a_param.clone(), b_param.clone()],
        vec![("test::Comparable".to_string(), super_template)],
        vec![],
    );

    let mut env = ClassEnv::<Ty, TyVar>::new();
    env.add_class("test::Pair".to_string(), class);

    let a_ty = Ty::con("int");
    let b_ty = Ty::con("string");
    let pair_ty = Ty::Projection(
        Box::new(Ty::con("test::Pair")),
        vec![a_ty.clone(), b_ty.clone()],
    );

    let predicate = Predicate::class(
        "test::Pair".to_string(),
        pair_ty,
        vec![a_ty.clone(), b_ty.clone()],
    );
    let supers = env.by_superclass(&predicate);

    let expected = Predicate::class(
        "test::Comparable".to_string(),
        Ty::Tuple(vec![b_ty, a_ty]),
        vec![],
    );

    assert!(
        supers.contains(&expected),
        "expected reordered predicate {:?} to appear in {:?}",
        expected,
        supers
    );
}

#[test]
fn supertraits_can_derive_complex_arguments() {
    let self_param = ty_var("test::PtrIter::Self");
    let elem_param = ty_var("test::PtrIter::Elem");

    let super_template = vec![Ty::Tuple(vec![
        Ty::refty(elem_param.clone()),
        Ty::con("usize"),
    ])];
    let class = Class::new(
        vec![self_param.clone(), elem_param.clone()],
        vec![("test::Iterable".to_string(), super_template)],
        vec![],
    );

    let mut env = ClassEnv::<Ty, TyVar>::new();
    env.add_class("test::PtrIter".to_string(), class);

    let elem_ty = Ty::con("char");
    let iter_ty = Ty::Projection(Box::new(Ty::con("test::PtrIter")), vec![elem_ty.clone()]);

    let predicate = Predicate::class("test::PtrIter".to_string(), iter_ty, vec![elem_ty.clone()]);
    let supers = env.by_superclass(&predicate);

    let expected = Predicate::class(
        "test::Iterable".to_string(),
        Ty::Tuple(vec![Ty::refty(elem_ty), Ty::con("usize")]),
        vec![],
    );

    assert!(
        supers.contains(&expected),
        "expected derived predicate {:?} to appear in {:?}",
        expected,
        supers
    );
}

#[test]
fn supertraits_chain_through_multiple_levels() {
    let iterable_self = ty_var("test::Iterable::Self");
    let iterable_super = vec![(
        "test::Sized".to_string(),
        vec![Ty::refty(iterable_self.clone())],
    )];
    let iterable_class = Class::new(vec![iterable_self.clone()], iterable_super, vec![]);

    let map_self = ty_var("test::Map::Self");
    let map_key = ty_var("test::Map::K");
    let map_val = ty_var("test::Map::V");
    let map_super = vec![(
        "test::Iterable".to_string(),
        vec![Ty::Tuple(vec![map_key.clone(), map_val.clone()])],
    )];
    let map_class = Class::new(
        vec![map_self.clone(), map_key.clone(), map_val.clone()],
        map_super,
        vec![],
    );

    let mut env = ClassEnv::<Ty, TyVar>::new();
    env.add_class("test::Iterable".to_string(), iterable_class);
    env.add_class("test::Map".to_string(), map_class);

    let key_ty = Ty::con("u8");
    let val_ty = Ty::con("u16");
    let map_ty = Ty::Projection(
        Box::new(Ty::con("test::Map")),
        vec![key_ty.clone(), val_ty.clone()],
    );

    let predicate = Predicate::class(
        "test::Map".to_string(),
        map_ty,
        vec![key_ty.clone(), val_ty.clone()],
    );
    let supers = env.by_superclass(&predicate);

    let iterable_expected = Predicate::class(
        "test::Iterable".to_string(),
        Ty::Tuple(vec![key_ty.clone(), val_ty.clone()]),
        vec![],
    );
    let sized_expected = Predicate::class(
        "test::Sized".to_string(),
        Ty::refty(Ty::Tuple(vec![key_ty, val_ty])),
        vec![],
    );

    assert!(
        supers.contains(&iterable_expected),
        "expected Iterable predicate {:?} in {:?}",
        iterable_expected,
        supers
    );
    assert!(
        supers.contains(&sized_expected),
        "expected Sized predicate {:?} in {:?}",
        sized_expected,
        supers
    );
}

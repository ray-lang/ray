use localti::{
    constraints::ConstraintGenError,
    context::TypeContext,
    types::{TAll, TFunc, TVar, Type},
};

fn main() -> Result<(), ConstraintGenError> {
    let mut tcx = TypeContext::new();
    let a = TVar("a".to_string());
    let int_ty = Type::Var(TVar("Int".to_string()));
    let num_ty = Type::Var(TVar("Num".to_string()));
    tcx.add_impl(int_ty.clone(), num_ty.clone());

    let ret_ty = tcx.infer_app(
        &TAll {
            tyvars: vec![(a.clone(), Some(vec![num_ty]))],
            ty: Box::new(Type::Func(TFunc {
                params: vec![Type::Var(a.clone()), Type::Var(a.clone())],
                ret_ty: Box::new(Type::Var(a.clone())),
            })),
        },
        vec![int_ty.clone(), int_ty.clone()],
    )?;

    println!("{}", ret_ty);
    Ok(())
}

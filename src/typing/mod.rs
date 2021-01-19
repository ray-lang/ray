#[macro_use]
mod macros;

mod bound;
mod context;
mod infer;
mod subst;

pub mod assumptions;
pub mod binding;
pub mod collect;
pub mod constraints;
pub mod info;
pub mod predicate;
pub mod solvers;
pub mod state;
pub mod traits;
pub mod ty;

pub use bound::*;
pub use context::*;
pub use infer::*;
pub use subst::*;

// #[cfg(test)]
// mod typing_test {
//     use super::{
//         ty::{LiteralKind, Ty, TyVar},
//         InferError, InferSystem,
//     };

//     macro_rules! t_unit {
//         () => {
//             Ty::Union(vec![])
//         };
//     }

//     macro_rules! t_nil {
//         () => {
//             Ty::Projection("nil".to_string(), vec![])
//         };
//     }

//     macro_rules! t_bool {
//         () => {
//             Ty::Projection("bool".to_string(), vec![])
//         };
//     }

//     macro_rules! t_int {
//         () => {
//             Ty::Projection("int".to_string(), vec![])
//         };
//     }

//     macro_rules! t_float {
//         () => {
//             Ty::Projection("float".to_string(), vec![])
//         };
//     }

//     macro_rules! t_ptr {
//         ($e:expr) => {
//             Ty::Projection("Ptr".to_string(), vec![$e])
//         };
//     }

//     macro_rules! check_ty {
//         ($inf:ident, $ex:ident, $expected_ty:expr) => {{
//             println!("getting type of: {}", $ex);
//             let (ex, _) = $inf.infer_ty($ex)?;
//             println!("checking against expected type:");
//             println!("expected: {}", $expected_ty);
//             println!("  actual: {}", ex.get_type());

//             assert_eq!(ex.get_type(), $expected_ty);
//         }};
//     }

//     macro_rules! check_ty_fail {
//         ($inf:ident, $ex:ident) => {{
//             println!("getting type of: {}", $ex);
//             let err = $inf.infer_ty($ex).err();
//             assert!(err.is_some());
//             println!("expected error: {:?}", err.unwrap());
//         }};
//     }

//     macro_rules! boxtvar {
//         ($($tv:tt)+) => {
//             Box::new(Ty::Var(tvar!($($tv)+)))
//         };
//     }

//     macro_rules! string {
//         ($x:expr) => {
//             $x.to_string()
//         };
//     }

//     macro_rules! def_ints {
//         ($ctx:ident) => {
//             for i in 0..=256 {
//                 $ctx.bind_var(i.to_string(), t_int!());
//             }
//         };
//     }

//     macro_rules! def_floats {
//         ($ctx:ident) => {{
//             let mut f = 0.0_f64;
//             while f < 10.0 {
//                 $ctx.bind_var(format!("{:.1}", f), t_float!());
//                 f += 0.1;
//             }
//         }};
//     }

//     type TestResult<T> = Result<(), InferError<T>>;

//     #[test]
//     fn test_malloc() -> TestResult<()> {
//         let mut ctx = mk_ctx! {
//             int_to_ptr => Ty::All(
//                 vec![tvar!(b)],
//                 Box::new(Ty::Func(
//                     vec![t_int!()],
//                     Box::new(t_ptr!(Ty::Var(tvar!(b)))),
//                 )),
//             ),
//             () => t_unit!(),
//             heap => t_int!(),
//             add => Ty::Func(vec![t_int!(), t_int!()], Box::new(t_int!())),
//             deref => Ty::All(
//                 vec![tvar!(c)],
//                 Box::new(Ty::Func(vec![
//                     t_ptr!(Ty::Var(tvar!(c)))
//                 ], Box::new(
//                     Ty::Var(tvar!(c))
//                 )))
//             )
//         };

//         def_ints!(ctx);

//         let e = mkexpr! {
//             let malloc = (fn [a] (size) => {
//                 int_to_ptr[('v a)](heap)
//             }) in (
//                 let p = (malloc[int](4)) in (
//                     p
//                 )
//             )
//         };

//         let inf = InferSystem::new(ctx);
//         check_ty!(inf, e, t_ptr!(t_int!()));

//         Ok(())
//     }

//     #[test]
//     fn test_union() -> TestResult<()> {
//         let mut ctx = mk_ctx! {
//             cond => Ty::All(
//                 vec![tvar!('x), tvar!('y)],
//                 Box::new(Ty::Func(vec![
//                     t_bool!(),
//                     Ty::Func(vec![], boxtvar!('x)),
//                     Ty::Func(vec![], boxtvar!('y)),
//                 ], Box::new(Ty::Union(vec![Ty::Var(tvar!('x)), Ty::Var(tvar!('y))]))))
//             ),
//             true => t_bool!(),
//             false => t_bool!(),
//             nil => t_nil!(),
//             eq => Ty::Func(vec![t_int!(), t_int!()], Box::new(t_bool!())),
//         };
//         def_ints!(ctx);

//         let inf = InferSystem::new(ctx);

//         let e = mkexpr! {
//             let f = (fn (x) => {
//                 let ( c = (eq(x, 1)),
//                       i = (fn () => { 2 } ),
//                       j = (fn () => { 4 } ) ) in (
//                     cond(c, i, j)
//                 )
//             }) in (
//                 f(3)
//             )
//         };

//         check_ty!(inf, e, t_int!());

//         let e = mkexpr! {
//             let f = (fn (x) => {
//                 let ( c = (eq(x, 1)),
//                       i = (fn () => { 2 } ),
//                       j = (fn () => { nil } ) ) in (
//                     cond(c, i, j)
//                 )
//             }) in (
//                 f(3)
//             )
//         };

//         check_ty!(inf, e, t_int!() | t_nil!());
//         Ok(())
//     }

//     #[test]
//     fn test_overload() -> TestResult<()> {
//         let ctx = mk_ctx! {
//             <= => Ty::Func(vec![t_int!(), t_int!()], Box::new(t_bool!())),
//             <= => Ty::All(vec![tvar!(a)], Box::new(
//                 Ty::Constrained(
//                     vec![(string!("<="), Ty::Func(vec![Ty::Var(tvar!(a)), Ty::Var(tvar!(a))], Box::new(t_bool!())))],
//                     Box::new(
//                         Ty::Func(vec![
//                             Ty::Projection(string!("seq"), vec![Ty::Var(tvar!(a))]),
//                             Ty::Projection(string!("seq"), vec![Ty::Var(tvar!(a))])
//                         ], Box::new(t_bool!()))
//                     )
//                 )
//             )),
//             c => Ty::Projection(string!("seq"), vec![t_int!()]),
//         };
//         let inf = InferSystem::new(ctx);

//         let e = mkexpr! {
//             let f = (fn (x) => {
//                 <=(x, x)
//             }) in (
//                 f(c)
//             )
//         };

//         check_ty!(inf, e, t_bool!());

//         let mut ctx = mk_ctx! {
//             == => Ty::Func(vec![t_int!(), t_int!()], Box::new(t_bool!())),
//             == => Ty::Func(vec![t_float!(), t_float!()], Box::new(t_bool!())),
//             / => Ty::Func(vec![t_int!(), t_int!()], Box::new(t_int!())),
//             / => Ty::Func(vec![t_int!(), t_int!()], Box::new(t_float!())),
//         };
//         def_ints!(ctx);
//         def_floats!(ctx);
//         let inf = InferSystem::new(ctx);

//         let e = mkexpr! {
//             let x = (/(3, 2)) in (
//                 ==(x, 3.1)
//             )
//         };

//         check_ty!(inf, e, t_bool!());

//         Ok(())
//     }

//     #[test]
//     fn test_int_subtype() -> TestResult<()> {
//         let ctx = mk_ctx! {
//             foo => Ty::Func(vec![Ty::u32(), Ty::i8()], Box::new(Ty::unit())),
//             1 => Ty::Literal(LiteralKind::Int, TyVar::new()),
//             2 => Ty::Literal(LiteralKind::Int, TyVar::new())
//         };

//         let e = mkexpr! {
//             foo(1, 2)
//         };

//         let inf = InferSystem::new(ctx);
//         check_ty!(inf, e, Ty::unit());
//         Ok(())
//     }

//     #[test]
//     fn test_constrained() -> TestResult<()> {
//         let t_seq = |x| Ty::Projection("seq".to_string(), vec![x]);
//         let ins = Ty::All(
//             vec![tvar!(b)],
//             Box::new(Ty::Constrained(
//                 vec![(
//                     str!("=="),
//                     Ty::Func(
//                         vec![Ty::Var(tvar!(b)), Ty::Var(tvar!(b))],
//                         Box::new(Ty::bool()),
//                     ),
//                 )],
//                 Box::new(Ty::Func(
//                     vec![Ty::Var(tvar!(b)), t_seq(Ty::Var(tvar!(b)))],
//                     Box::new(t_seq(Ty::Var(tvar!(b)))),
//                 )),
//             )),
//         );

//         let list = Ty::All(
//             vec![tvar!(a)],
//             Box::new(Ty::Func(
//                 vec![Ty::Var(tvar!(a))],
//                 Box::new(t_seq(Ty::Var(tvar!(a)))),
//             )),
//         );

//         let ctx = mk_ctx! {
//             == => Ty::Func(vec![Ty::int(), Ty::int()], Box::new(Ty::bool())),
//             == => Ty::Func(vec![Ty::float(), Ty::float()], Box::new(Ty::bool())),
//             ins => ins,
//             list => list,
//             1 => Ty::int(),
//             2 => Ty::int(),
//             3 => Ty::int(),
//             true => Ty::bool(),
//             false => Ty::bool(),
//         };
//         let e = mkexpr! {
//             let l = (list(1)) in (
//                 ins(2, l)
//             )
//         };

//         let inf = InferSystem::new(ctx);
//         check_ty!(inf, e, t_seq(Ty::int()));

//         let e = mkexpr! {
//             let l = (list(true)) in (
//                 ins(false, l)
//             )
//         };

//         check_ty_fail!(inf, e);

//         Ok(())
//     }
// }

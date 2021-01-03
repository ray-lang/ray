use crate::ast::Module;

use super::constraints::tree::ConstraintTree;

pub fn infer(module: &Module) {
    // let mut inf = Infer {
    //     constraints: ConstraintTree::empty(),
    // };

    // collect constraints from the module into a tree
    let ct = ConstraintTree::empty();
    // let cs = ct.flatten();
}

#[cfg(test)]
mod infer_test {
    use std::collections::HashSet;

    use crate::typing::{
        top::{
            constraints::{tree::BottomUpWalk, CollectConstraints},
            hm,
            solvers::{GreedySolver, Solver},
            state::TyVarFactory,
            traits::HasSubst,
        },
        ty::Ty,
    };

    #[test]
    fn infer_lit_id() -> Result<(), String> {
        // let id = λx.x in (i 1)
        let ex = hm::Expr::Let(
            str!("id"),
            Box::new(hm::Expr::Abs(
                vec![str!("x")],
                Box::new(hm::Expr::Var(str!("x"))),
            )),
            Box::new(hm::Expr::App(
                Box::new(hm::Expr::Var(str!("id"))),
                vec![hm::Expr::Lit(hm::LitKind::Int)],
            )),
        );

        let mut tf = TyVarFactory::new("v");
        let mono_tys = HashSet::new();
        let (ty, _, ct) = ex.collect_constraints(&mono_tys, &mut tf);

        println!("ty = {}", ty);
        println!("ct = {:#?}", ct);
        let cs = ct.flatten(BottomUpWalk);
        println!("{:?}", cs);
        let mut sf = TyVarFactory::new("s");
        let mut solver = GreedySolver::new(&mut tf, &mut sf, cs);
        solver.start_solving()?;
        println!("{}", solver.get_subst());

        if let Ty::Var(v) = ty {
            let sub = solver.get_subst();
            let t = sub.get(&v).expect("expected variable in substitution");
            assert_eq!(t, &Ty::int());
        } else {
            panic!("expected type variable but found {}", ty);
        }

        Ok(())
    }

    #[test]
    fn infer_lambda_id() -> Result<(), String> {
        // let id = λx.x in (id id)
        let ex = hm::Expr::Let(
            str!("id"),
            Box::new(hm::Expr::Abs(
                vec![str!("x")],
                Box::new(hm::Expr::Var(str!("x"))),
            )),
            Box::new(hm::Expr::App(
                Box::new(hm::Expr::Var(str!("id"))),
                vec![hm::Expr::Var(str!("id"))],
            )),
        );

        let mut tf = TyVarFactory::new("v");
        let (ty, _, ct) = ex.collect_constraints(&HashSet::new(), &mut tf);
        println!("ty = {}", ty);
        println!("ct = {:#?}", ct);
        let cs = ct.flatten(BottomUpWalk);
        println!("{:?}", cs);
        let mut svar_factory = TyVarFactory::new("s");
        let mut solver = GreedySolver::new(&mut tf, &mut svar_factory, cs);
        solver.start_solving()?;
        println!("{}", solver.get_subst());

        Ok(())
    }
}

use crate::typing::{
    predicate::TyPredicate,
    top::solvers::Solution,
    ty::{Ty, TyVar},
    ApplySubst, FormalizeTypes, Subst,
};

use super::{HirDecl, HirDeclKind, HirNode, HirNodeKind, TypedHirNode};

impl FormalizeTypes for HirNode {
    fn formalize(self, solution: &mut Solution) -> HirNode {
        let src = self.src;
        let kind = match self.kind {
            HirNodeKind::Var(v) => HirNodeKind::Var(v),
            HirNodeKind::Literal(lit) => HirNodeKind::Literal(lit),
            HirNodeKind::Type(t) => HirNodeKind::Type(t),
            HirNodeKind::Cast(d, t) => HirNodeKind::Cast(d.formalize(solution), t),
            HirNodeKind::Decl(d) => HirNodeKind::Decl(d.formalize(solution)),
            HirNodeKind::Struct(s, f) => HirNodeKind::Struct(s, f),
            HirNodeKind::Block(stmts) => HirNodeKind::Block(stmts.formalize(solution)),
            HirNodeKind::Let(decls, body) => {
                HirNodeKind::Let(decls.formalize(solution), body.formalize(solution))
            }
            HirNodeKind::Fun(params, body) => HirNodeKind::Fun(params, body.formalize(solution)),
            HirNodeKind::Apply(fun, args) => {
                HirNodeKind::Apply(fun.formalize(solution), args.formalize(solution))
            }
            HirNodeKind::Typed(t) => HirNodeKind::Typed(t.formalize(solution)),
        };

        HirNode { kind, src }
    }
}

impl FormalizeTypes for TypedHirNode {
    fn formalize(self, solution: &mut Solution) -> Self {
        let (ex, ty) = self.take();
        if matches!(&ex.kind, HirNodeKind::Fun(_, _)) {
            let ty: Ty = ty.clone().apply_subst(&solution.subst);
            if let Ok((_, _, param_tys, ret_ty)) = ty.try_borrow_fn() {
                // bind all type variables in the function type
                let mut subst = Subst::new();
                let mut c = 'a' as u8;
                for p in param_tys.iter().chain(std::iter::once(ret_ty)) {
                    if let Ty::Var(v) = p {
                        if !subst.contains_key(v) {
                            let u = Ty::Var(TyVar(format!("'{}", c as char).into()));
                            subst.insert(v.clone(), u);
                            c += 1;
                        }
                    }
                }

                // add the substition to the solution
                solution.subst.extend(subst);
            } else if let Ty::All(_, t) = ty {
                let mut subst = Subst::new();
                let (preds, ty) = t.unpack_qualified_ty();
                for p in preds {
                    if let Ty::Var(v) = &ty {
                        if p.is_int_trait() {
                            subst.insert(v.clone(), Ty::int());
                            break;
                        } else if p.is_float_trait() {
                            subst.insert(v.clone(), Ty::float());
                            break;
                        }
                    }
                }

                // add the substition to the solution
                solution.subst.extend(subst);
            }
        }

        TypedHirNode::new(ex.formalize(solution), ty)
    }
}

impl FormalizeTypes for HirDecl {
    fn formalize(self, solution: &mut Solution) -> Self {
        let src = self.src;
        let kind = match self.kind {
            HirDeclKind::Pattern(p, t) => HirDeclKind::Pattern(p, t.formalize(solution)),
            HirDeclKind::Type(s, t) => HirDeclKind::Type(s, t),
        };
        HirDecl { kind, src }
    }
}

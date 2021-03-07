use std::collections::HashSet;

use crate::{
    ast::{Node, Path},
    span::SourceMap,
    ssa::{BasicOp, BasicOpKind, Op, Size},
    typing::{
        assumptions::AssumptionSet,
        collect::CollectConstraints,
        constraints::tree::{ConstraintTree, ReceiverTree},
        ty::{Ty, TyVar},
        TyCtx,
    },
    utils::{indent, join, map_join},
};

pub enum LValue {
    Var(usize),
    Label(usize),
    Func(String),
    Op(Op),
}

impl std::fmt::Display for LValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LValue::Var(v) => write!(f, "${}", v),
            LValue::Label(l) => write!(f, "L{}", l),
            LValue::Func(n) => write!(f, "{}", n),
            LValue::Op(op) => write!(f, "{}", op),
        }
    }
}

pub enum Value {
    Unit,
    PointerSize,
    Var(usize),
    Data(usize),
    Uint(u64, Ty),
    Int(i64, Ty),
    Ty(Ty),
    Size(Size),
    Sizeof(Ty),
    AsmOp(BasicOpKind, Size, bool, Vec<Value>),
    GetField(Box<Node<Value>>, String),
    If(Node<usize>, Box<Node<Value>>, Box<Node<Value>>),
    Apply(Node<LValue>, Vec<Node<Value>>),
    Lambda(Vec<Node<usize>>, Box<Node<Value>>),
    Let(Vec<(Node<LValue>, Node<Value>)>, Box<Node<Value>>),
    LetRec(Vec<(Node<LValue>, Node<Value>)>, Box<Node<Value>>),
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Unit => write!(f, "()"),
            Value::PointerSize => write!(f, "ptrsize"),
            Value::Var(v) => write!(f, "${}", v),
            Value::Data(d) => write!(f, "$data[{}]", d),
            Value::AsmOp(op, _, _, operands) => {
                write!(f, "({} {})", op, join(operands, " "))
            }
            Value::Apply(lhs, args) => {
                if args.len() > 0 {
                    write!(f, "({} {})", lhs, join(args, " "))
                } else {
                    write!(f, "({})", lhs)
                }
            }
            Value::If(cond, then_value, else_value) => {
                write!(f, "(if ${} then {} else {})", cond, then_value, else_value)
            }
            Value::Lambda(params, body) => write!(
                f,
                "λ({}) => {}",
                map_join(params, ", ", |p| format!("${}", p)),
                body
            ),
            Value::Let(defs, body) => write!(
                f,
                "let\n{}\nin\n{}",
                indent(
                    map_join(defs, "\n", |(lhs, rhs)| format!("{} = {}", lhs, rhs)),
                    2
                ),
                indent(body.to_string(), 2)
            ),
            Value::LetRec(defs, body) => write!(
                f,
                "letrec\n{}\nin\n{}",
                indent(
                    map_join(defs, "\n", |(lhs, rhs)| format!("{} = {}", lhs, rhs)),
                    2
                ),
                body
            ),
            Value::Uint(i, _) => write!(f, "{}", i),
            Value::Int(i, _) => write!(f, "{}", i),
            Value::Ty(ty) => write!(f, "{}", ty),
            Value::Size(s) => write!(f, "{}", s),
            Value::Sizeof(ty) => write!(f, "sizeof({})", ty),
            Value::GetField(lhs, field) => write!(f, "(getfield {} {})", lhs, field),
        }
    }
}

impl CollectConstraints for Node<Value> {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let src = srcmap.get(self);
        match &self.value {
            Value::Unit => (Ty::unit(), AssumptionSet::new(), ConstraintTree::empty()),
            Value::Size(_) | Value::Sizeof(_) | Value::PointerSize => {
                (Ty::uint(), AssumptionSet::new(), ConstraintTree::empty())
            }
            Value::Var(loc) => {
                let ty = tcx.ty_of(self.id);
                let label = ty.to_string();
                let mut aset = AssumptionSet::new();
                aset.add(Path::from(format!("${}", loc)), ty.clone());
                (ty, aset, ReceiverTree::new(label))
            }
            Value::Data(_) => todo!(),
            Value::Uint(_, ty) | Value::Int(_, ty) | Value::Ty(ty) => {
                (ty.clone(), AssumptionSet::new(), ConstraintTree::empty())
            }
            Value::AsmOp(_, _, _, _) => todo!(),
            Value::GetField(_, _) => todo!(),
            Value::If(_, _, _) => todo!(),
            Value::Apply(_, _) => todo!(),
            Value::Lambda(_, _) => todo!(),
            Value::Let(_, _) => todo!(),
            Value::LetRec(_, _) => todo!(),
        }
    }
}

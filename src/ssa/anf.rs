use std::collections::{HashMap, HashSet};

use crate::{
    anf,
    ast::{Module, Node},
    graph::Graph,
};

use super::{Block, Callable, Expr, Func, Value};

pub fn to_anf_module(funcs: &Vec<Node<Func>>) -> Node<anf::Value> {
    let funcs = funcs
        .iter()
        .map(|func| {
            (
                Node::new(anf::LValue::Func(func.name.to_string())),
                func.to_anf(),
            )
        })
        .collect();

    Node::new(anf::Value::LetRec(
        funcs,
        Box::new(Node::new(anf::Value::Apply(
            Node::new(anf::LValue::Func(str!("main"))),
            vec![],
        ))),
    ))
}

pub trait ToANF {
    type Output;

    fn to_anf(&self) -> Self::Output;
}

impl ToANF for Node<Func> {
    type Output = Node<anf::Value>;

    fn to_anf(&self) -> Self::Output {
        fn arg_list(block: &Block, label: usize) -> Vec<Node<anf::Value>> {
            block
                .get_expr()
                .iter()
                .filter_map(|ex| match &ex.value {
                    Expr::Phi(_, pairs) => {
                        for (other, var) in pairs.iter() {
                            if other == &label {
                                return Some(var.map(|&loc| anf::Value::Var(loc)));
                            }
                        }
                        None
                    }
                    _ => None,
                })
                .chain(
                    block
                        .used_vars()
                        .iter()
                        .map(|&loc| Node::new(anf::Value::Var(loc))),
                )
                .collect()
        }

        fn mk_apply(
            blocks: &Vec<Block>,
            target_label: usize,
            src_label: usize,
        ) -> Node<anf::Value> {
            let block = &blocks[target_label];
            Node::new(anf::Value::Apply(
                Node::new(anf::LValue::Label(target_label)),
                arg_list(block, src_label),
            ))
        }

        fn convert_block(
            blocks: &Vec<Block>,
            label: usize,
            block: &Block,
        ) -> (Node<anf::LValue>, Node<anf::Value>) {
            let params = block
                .get_expr()
                .iter()
                .filter_map(|ex| {
                    if let Expr::Phi(loc, _) = &ex.value {
                        Some(loc.clone())
                    } else {
                        None
                    }
                })
                .chain(block.used_vars().iter().map(|&loc| Node::new(loc)))
                .collect();
            let body =
                block
                    .get_expr()
                    .iter()
                    .rev()
                    .fold(Node::new(anf::Value::Unit), |mut body, ex| {
                        match &ex.value {
                            Expr::Set(lhs, rhs) => {
                                let def = (lhs.map(|&loc| anf::LValue::Var(loc)), rhs.to_anf());
                                if let anf::Value::Let(defs, _) = &mut body.value {
                                    defs.insert(0, def);
                                } else {
                                    return Node::new(anf::Value::Let(vec![def], Box::new(body)));
                                }

                                body
                            }
                            Expr::Phi(..) => body,
                            Expr::Goto(other_label) => mk_apply(blocks, other_label.value, label),
                            Expr::Ret(v) => v.to_anf(),
                            Expr::If(cond, then_label, else_label) => Node::new(anf::Value::If(
                                cond.clone(),
                                Box::new(mk_apply(blocks, then_label.value, label)),
                                Box::new(mk_apply(blocks, else_label.value, label)),
                            )),
                        }
                    });
            (
                Node::new(anf::LValue::Label(label)),
                Node::new(anf::Value::Lambda(params, Box::new(body))),
            )
        }

        if self.blocks.len() == 0 {
            return Node::with_id(self.id, anf::Value::Unit);
        }

        let decls = self
            .blocks
            .iter()
            .enumerate()
            .map(|(label, block)| convert_block(&self.blocks, label, block))
            .collect::<Vec<_>>();

        Node::with_id(
            self.id,
            anf::Value::LetRec(
                decls,
                Box::new(Node::new(anf::Value::Apply(
                    Node::new(anf::LValue::Label(0)),
                    arg_list(&self.blocks[0], 0),
                ))),
            ),
        )
    }
}

impl ToANF for Node<Value> {
    type Output = Node<anf::Value>;

    fn to_anf(&self) -> Self::Output {
        let id = self.id;
        let value = self.value.to_anf();
        Node::with_id(id, value)
    }
}

impl ToANF for Value {
    type Output = anf::Value;

    fn to_anf(&self) -> Self::Output {
        match &self {
            Value::Local(loc) => anf::Value::Var(*loc),
            Value::Data(data) => anf::Value::Data(*data),
            Value::Uint(i, ty) => anf::Value::Uint(*i, ty.clone()),
            Value::Int(i, ty) => anf::Value::Int(*i, ty.clone()),
            Value::Ty(ty) => anf::Value::Ty(ty.clone()),
            Value::Size(size) => anf::Value::Size(size.clone()),
            Value::Sizeof(ty) => anf::Value::Sizeof(ty.clone()),
            Value::FieldOf(lhs, field) => anf::Value::GetField(
                Box::new(lhs.map(|loc| anf::Value::Var(*loc))),
                field.clone(),
            ),
            Value::Call(lhs, args) => {
                let lhs = lhs.map(|v| match v {
                    Callable::Name(n) => anf::LValue::Func(n.to_string()),
                    Callable::Op(op) => anf::LValue::Op(*op),
                });

                anf::Value::Apply(lhs, args.to_anf())
            }
            Value::BasicOp(op) => {
                anf::Value::AsmOp(op.op, op.size, op.signed, op.operands.to_anf())
            }
            Value::PointerSize => anf::Value::PointerSize,
            Value::Empty => anf::Value::Unit,
        }
    }
}

impl<T, U> ToANF for Vec<T>
where
    T: ToANF<Output = U>,
{
    type Output = Vec<U>;

    fn to_anf(&self) -> Self::Output {
        self.iter().map(|n| n.to_anf()).collect()
    }
}

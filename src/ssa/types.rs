use std::collections::HashSet;

use crate::{
    ast::{Node, Path},
    graph::Graph,
    typing::ty::Ty,
    utils::{indent, join, map_join, replace},
};

pub use super::basic_op::*;
pub use super::size::*;

#[derive(Debug, Clone)]
pub struct Param {
    name: String,
    ty: Ty,
}

impl std::fmt::Display for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.ty)
    }
}

#[derive(Debug, Clone)]
pub struct Local {
    pub(in crate::ssa) idx: usize,
    pub(in crate::ssa) ty: Ty,
}

impl std::fmt::Display for Local {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.idx)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Op {
    Add,
    Mul,
    Div,
    Store,
    Malloc,
    MemCopy,
}

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Op::Add => write!(f, "add"),
            Op::Mul => write!(f, "mul"),
            Op::Div => write!(f, "div"),
            Op::Store => write!(f, "store"),
            Op::Malloc => write!(f, "malloc"),
            Op::MemCopy => write!(f, "memcopy"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Callable {
    Name(Path),
    Op(Op),
}

impl std::fmt::Display for Callable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Callable::Name(p) => write!(f, "{}", p),
            Callable::Op(op) => write!(f, "{}", op),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Local(usize),
    Data(usize),
    Uint(u64, Ty),
    Int(i64, Ty),
    Ty(Ty),
    Size(Size),
    Sizeof(Ty),
    FieldOf(Node<usize>, String),
    Call(Node<Callable>, Vec<Node<Value>>),
    BasicOp(BasicOp),
    PointerSize,
    Empty,
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Local(loc) => write!(f, "${}", loc),
            Value::Data(d) => write!(f, "$data[{}]", d),
            Value::Uint(c, _) => write!(f, "{}", c),
            Value::Int(c, _) => write!(f, "{}", c),
            Value::Ty(ty) => write!(f, "{}", ty),
            Value::Sizeof(ty) => write!(f, "sizeof({})", ty),
            Value::Size(s) => write!(f, "{}", s),
            Value::FieldOf(loc, field) => write!(f, "field(${}, {})", loc, field),
            Value::Call(lhs, args) => write!(f, "{}({})", lhs, join(args, ", ")),
            Value::BasicOp(op) => write!(f, "{}", op),
            Value::PointerSize => write!(f, "sizeof(ptr['a])"),
            Value::Empty => write!(f, ""),
        }
    }
}

impl std::ops::Add for Value {
    type Output = Value;

    fn add(self, rhs: Self) -> Self::Output {
        Value::Call(
            Node::new(Callable::Op(Op::Add)),
            vec![Node::new(self), Node::new(rhs)],
        )
    }
}

impl std::ops::Add<usize> for Value {
    type Output = Value;

    fn add(self, rhs: usize) -> Self::Output {
        Value::Call(
            Node::new(Callable::Op(Op::Add)),
            vec![
                Node::new(self),
                Node::new(Value::Uint(rhs as u64, Ty::uint())),
            ],
        )
    }
}

impl std::ops::Mul<usize> for Value {
    type Output = Value;

    fn mul(self, rhs: usize) -> Self::Output {
        Value::Call(
            Node::new(Callable::Op(Op::Mul)),
            vec![
                Node::new(self),
                Node::new(Value::Uint(rhs as u64, Ty::uint())),
            ],
        )
    }
}

impl std::ops::Div<usize> for Value {
    type Output = Value;

    fn div(self, rhs: usize) -> Self::Output {
        Value::Call(
            Node::new(Callable::Op(Op::Div)),
            vec![
                Node::new(self),
                Node::new(Value::Uint(rhs as u64, Ty::uint())),
            ],
        )
    }
}

impl std::ops::AddAssign for Value {
    fn add_assign(&mut self, rhs: Self) {
        replace(self, |lhs| lhs + rhs)
    }
}

impl Into<Value> for usize {
    fn into(self) -> Value {
        Value::Uint(self as u64, Ty::uint())
    }
}

impl Value {
    pub fn zero() -> Value {
        Value::Uint(0, Ty::uint())
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    Set(Node<usize>, Node<Value>),
    Phi(Node<usize>, Vec<(usize, Node<usize>)>),
    Goto(Node<usize>),
    Ret(Node<Value>),
    If(Node<usize>, Node<usize>, Node<usize>),
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Set(loc, value) => write!(f, "${} = {}", loc, value),
            Expr::Phi(loc, labels) => write!(
                f,
                "${} = phi({})",
                loc,
                map_join(labels, ", ", |(l, v)| { format!("L{}: ${}", l, v) })
            ),
            Expr::Goto(label) => write!(f, "goto L{}", label),
            Expr::Ret(val) => write!(f, "ret {}", val),
            Expr::If(cond, then, els) => write!(f, "if ${} L{} L{}", cond, then, els),
        }
    }
}

impl Expr {
    #[inline(always)]
    pub fn is_control(&self) -> bool {
        matches!(self, Expr::Goto(_) | Expr::Ret(_) | Expr::If(..))
    }
}

#[derive(Clone, Debug)]
pub struct Extern {
    pub name: Path,
    pub ty: Ty,
    pub is_mutable: bool,
    pub src: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Func {
    pub name: Path,
    pub params: Vec<(String, Ty)>,
    pub locals: Vec<Local>,
    pub blocks: Vec<Block>,
    pub data: Vec<Vec<u8>>,
    pub cfg: Graph<usize, HashSet<usize>>,
}

impl std::fmt::Display for Func {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(fn {}({})\n{}\n)",
            self.name,
            map_join(self.params.iter().enumerate(), ", ", |(i, (p, _))| format!(
                "{}: ${}",
                p, i
            )),
            join(&self.blocks, "\n")
        )
    }
}

impl Func {
    #[allow(dead_code)]
    pub fn calculate_dominators(&mut self) {
        for (idx, block) in self.blocks.iter().enumerate() {
            log::debug!("block = {}", block);
            let dom = self.cfg.dominates(&idx);
            log::debug!("dom = {:?}", dom);
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    label: usize,
    expr: Vec<Node<Expr>>,
    def_set: Vec<usize>,
    use_set: Vec<usize>,
}

impl std::fmt::Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "L{}: {{ def_set: {:?}, use_set: {:?} }}\n{}",
            self.label,
            self.def_set,
            self.use_set,
            indent(join(&self.expr, "\n"), 2)
        )
    }
}

impl Block {
    pub(super) fn new(label: usize) -> Block {
        Block {
            label,
            expr: vec![],
            def_set: vec![],
            use_set: vec![],
        }
    }

    #[inline(always)]
    pub fn get_expr(&self) -> &Vec<Node<Expr>> {
        &self.expr
    }

    #[inline(always)]
    pub fn push(&mut self, value: Node<Expr>) {
        self.expr.push(value);
    }

    #[inline(always)]
    pub fn last(&mut self) -> Option<&Node<Expr>> {
        self.expr.last()
    }

    #[inline(always)]
    #[allow(dead_code)]
    pub fn last_mut(&mut self) -> Option<&mut Node<Expr>> {
        self.expr.last_mut()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.expr.is_empty()
    }

    #[inline(always)]
    pub fn use_var(&mut self, loc: usize) {
        if !self.use_set.contains(&loc) && !self.def_set.contains(&loc) {
            self.use_set.push(loc);
        }
    }

    #[inline(always)]
    pub fn def_var(&mut self, loc: usize) {
        if !self.def_set.contains(&loc) {
            self.def_set.push(loc);
        }
    }

    #[inline(always)]
    pub fn used_vars(&self) -> &Vec<usize> {
        &self.use_set
    }

    // #[inline(always)]
    // pub fn vars(&self) -> &HashMap<String, usize> {
    //     &self.vars
    // }

    // #[inline(always)]
    // pub fn get_var(&mut self, name: &String) -> Option<&usize> {
    //     self.vars.get(name)
    // }

    // #[inline(always)]
    // pub fn set_var(&mut self, name: String, idx: usize) {
    //     self.vars.insert(name, idx);
    // }
}

use ast::Decorator;
use itertools::Itertools;

use crate::{
    ast::{self, asm::AsmOp, Node, Path, SourceInfo},
    strutils::indent_lines,
    typing::{ty::Ty, ApplySubst, Subst},
    utils::{join, map_join},
};

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    iter::Sum,
    rc::Rc,
};

use super::optimize;

macro_rules! LirImplInto {
    ($dst:ident for $src:ident) => {
        impl Into<$dst> for $src {
            fn into(self) -> $dst {
                $dst::$src(self)
            }
        }
    };
}

pub trait NamedInst {
    fn get_name(&self) -> &Path;
    fn set_name(&mut self, name: Path);
}

pub trait GetLocals<'a> {
    fn get_locals(&'a self) -> Vec<&'a usize>;
}

impl<'a, T> GetLocals<'a> for Vec<T>
where
    T: GetLocals<'a> + 'a,
{
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.iter().flat_map(|t| t.get_locals()).collect()
    }
}

impl<'a, I> GetLocals<'a> for Node<Inst, I> {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.value.get_locals()
    }
}

pub trait GetLocalsMut<'a> {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize>;
}

impl<'a, T> GetLocalsMut<'a> for Vec<T>
where
    T: GetLocalsMut<'a> + 'a,
{
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.iter_mut().flat_map(|t| t.get_locals_mut()).collect()
    }
}

impl<'a, I> GetLocalsMut<'a> for Node<Inst, I> {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.value.get_locals_mut()
    }
}

pub trait OffsetLocals<'a> {
    fn offset_locals(&'a mut self, offset: usize);
}

impl<'a, T> OffsetLocals<'a> for T
where
    T: GetLocalsMut<'a>,
{
    fn offset_locals(&'a mut self, offset: usize) {
        for loc in self.get_locals_mut() {
            *loc += offset;
        }
    }
}

pub trait MapLocals<'a> {
    fn map_locals(&'a mut self, local_map: &HashMap<usize, usize>);
}

impl<'a, T> MapLocals<'a> for T
where
    T: GetLocalsMut<'a>,
{
    fn map_locals(&'a mut self, local_map: &HashMap<usize, usize>) {
        for local in self.get_locals_mut() {
            if let Some(i) = local_map.get(local) {
                *local = *i;
            }
        }
    }
}

pub type SymbolSet = HashSet<Path>;

impl ApplySubst for SymbolSet {
    fn apply_subst(self, subst: &Subst) -> Self {
        self.into_iter().map(|p| p.apply_subst(subst)).collect()
    }
}

#[derive(Clone, Debug)]
pub struct TypeMetadata;

#[derive(Clone, Debug)]
pub enum Variable {
    Data(usize),
    Global(usize),
    Local(usize),
}

LirImplInto!(Atom for Variable);

impl Into<Value> for Variable {
    fn into(self) -> Value {
        Value::new(Atom::Variable(self))
    }
}

impl std::fmt::Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Variable::Data(s) => write!(f, "$data[{}]", s),
            Variable::Global(s) => write!(f, "$global[{}]", s),
            Variable::Local(s) => write!(f, "${}", s),
        }
    }
}

impl<'a> GetLocalsMut<'a> for Variable {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        if let Variable::Local(i) = self {
            vec![i]
        } else {
            vec![]
        }
    }
}

impl<'a> GetLocals<'a> for Variable {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        if let Variable::Local(i) = self {
            vec![i]
        } else {
            vec![]
        }
    }
}

impl ApplySubst for Variable {
    fn apply_subst(self, subst: &Subst) -> Self {
        self
    }
}

#[derive(Clone, Debug)]
pub enum Atom {
    Variable(Variable),
    FuncRef(FuncRef),
    Size(Size),
    UintConst(u64, Size),
    IntConst(i64, Size),
    FloatConst(f64, Size),
    RawString(String),
    NilConst,
}

LirImplInto!(Value for Atom);

impl std::fmt::Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Atom::Variable(v) => write!(f, "{}", v),
            Atom::FuncRef(r) => write!(f, "{}", r),
            Atom::Size(s) => write!(f, "{}", s),
            Atom::UintConst(u, _) => write!(f, "{}", u),
            Atom::IntConst(i, _) => write!(f, "{}", i),
            Atom::FloatConst(c, _) => write!(f, "{}", c),
            Atom::RawString(s) => write!(f, "{:?}", s),
            Atom::NilConst => write!(f, "nil"),
        }
    }
}

impl<'a> GetLocalsMut<'a> for Atom {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        match self {
            Atom::Variable(v) => v.get_locals_mut(),
            Atom::FuncRef(_)
            | Atom::Size(_)
            | Atom::UintConst(_, _)
            | Atom::IntConst(_, _)
            | Atom::FloatConst(_, _)
            | Atom::RawString(_)
            | Atom::NilConst => vec![],
        }
    }
}

impl<'a> GetLocals<'a> for Atom {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        match self {
            Atom::Variable(v) => v.get_locals(),
            Atom::FuncRef(_)
            | Atom::Size(_)
            | Atom::UintConst(_, _)
            | Atom::IntConst(_, _)
            | Atom::FloatConst(_, _)
            | Atom::RawString(_)
            | Atom::NilConst => vec![],
        }
    }
}

impl ApplySubst for Atom {
    fn apply_subst(self, subst: &Subst) -> Self {
        match self {
            Atom::Variable(v) => Atom::Variable(v.apply_subst(subst)),
            Atom::FuncRef(r) => Atom::FuncRef(r.apply_subst(subst)),
            t @ _ => t,
        }
    }
}

impl Atom {
    pub fn new<A: Into<Atom>>(a: A) -> Atom {
        a.into()
    }
}

#[derive(Clone, Debug)]
pub struct Malloc(pub Atom);
LirImplInto!(Value for Malloc);

impl std::fmt::Display for Malloc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "malloc({})", self.0)
    }
}

impl<'a> GetLocals<'a> for Malloc {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.0.get_locals()
    }
}

impl<'a> GetLocalsMut<'a> for Malloc {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.0.get_locals_mut()
    }
}

impl ApplySubst for Malloc {
    fn apply_subst(self, subst: &Subst) -> Self {
        self
    }
}

impl Malloc {
    pub fn new<A: Into<Atom>>(a: A) -> Value {
        Malloc(a.into()).into()
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Empty,
    Atom(Atom),
    Malloc(Malloc),
    Call(Call),
    CExternCall(CExternCall),
    Branch(Branch),
    Select(Select),
    Load(Load),
    Lea(Lea),
    GetField(GetField),
    BasicOp(BasicOp),
    IntConvert(IntConvert),
}

LirImplInto!(Inst for Value);

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Empty => write!(f, ""),
            Value::Atom(a) => write!(f, "{}", a),
            Value::Malloc(a) => write!(f, "{}", a),
            Value::Call(a) => write!(f, "{}", a),
            Value::CExternCall(a) => write!(f, "{}", a),
            Value::Branch(a) => write!(f, "{}", a),
            Value::Select(a) => write!(f, "{}", a),
            Value::Load(a) => write!(f, "{}", a),
            Value::Lea(a) => write!(f, "{}", a),
            Value::GetField(a) => write!(f, "{}", a),
            Value::BasicOp(a) => write!(f, "{}", a),
            Value::IntConvert(a) => write!(f, "{}", a),
        }
    }
}

impl<'a> GetLocalsMut<'a> for Value {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        match self {
            Value::Atom(a) => a.get_locals_mut(),
            Value::Call(c) => c.get_locals_mut(),
            Value::CExternCall(c) => c.get_locals_mut(),
            Value::Branch(b) => b.get_locals_mut(),
            Value::Select(s) => s.get_locals_mut(),
            Value::Load(l) => l.get_locals_mut(),
            Value::Malloc(m) => m.get_locals_mut(),
            Value::Lea(l) => l.get_locals_mut(),
            Value::GetField(g) => g.get_locals_mut(),
            Value::BasicOp(b) => b.get_locals_mut(),
            Value::IntConvert(_) => todo!(),
            Value::Empty => vec![],
        }
    }
}

impl<'a> GetLocals<'a> for Value {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        match self {
            Value::Atom(a) => a.get_locals(),
            Value::Call(c) => c.get_locals(),
            Value::CExternCall(c) => c.get_locals(),
            Value::Branch(b) => b.get_locals(),
            Value::Select(s) => s.get_locals(),
            Value::Load(l) => l.get_locals(),
            Value::Lea(l) => l.get_locals(),
            Value::GetField(g) => g.get_locals(),
            Value::BasicOp(b) => b.get_locals(),
            Value::IntConvert(_) => todo!(),
            Value::Malloc(_) | Value::Empty => vec![],
        }
    }
}

impl ApplySubst for Value {
    fn apply_subst(self, subst: &Subst) -> Value {
        match self {
            Value::Empty => Value::Empty,
            Value::Atom(a) => Value::Atom(a.apply_subst(subst)),
            Value::Malloc(m) => Value::Malloc(m.apply_subst(subst)),
            Value::Call(c) => Value::Call(c.apply_subst(subst)),
            Value::CExternCall(_) => todo!(),
            Value::Branch(b) => Value::Branch(b.apply_subst(subst)),
            Value::Select(s) => Value::Select(s.apply_subst(subst)),
            Value::Load(l) => Value::Load(l.apply_subst(subst)),
            Value::Lea(l) => Value::Lea(l.apply_subst(subst)),
            Value::GetField(g) => Value::GetField(g.apply_subst(subst)),
            Value::BasicOp(b) => Value::BasicOp(b.apply_subst(subst)),
            Value::IntConvert(i) => Value::IntConvert(i.apply_subst(subst)),
        }
    }
}

impl NamedInst for Value {
    fn get_name(&self) -> &Path {
        match self {
            Value::Call(c) => &c.fn_name,
            _ => panic!("{} is unnamed", self),
        }
    }

    fn set_name(&mut self, name: Path) {
        match self {
            Value::Call(c) => c.fn_name = name,
            _ => panic!("{} is unnamed", self),
        }
    }
}

impl Value {
    pub fn new<V>(v: V) -> Value
    where
        V: Into<Value>,
    {
        v.into()
    }
}

#[derive(Clone, Debug)]
pub enum Inst {
    Value(Value),
    Free(usize),
    SetGlobal(usize, Value),
    SetLocal(usize, Value),
    Block(Block),
    Func(Func),
    IfBlock(IfBlock),
    Loop(Loop),
    Store(Store),
    MemCopy(Variable, Variable, Variable),
    IncRef(Value, i8),
    DecRef(Value),
    Return(Value),
    Break,
    Halt,
}

impl std::fmt::Display for Inst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Inst::Value(v) => write!(f, "{}", v),
            Inst::Free(s) => write!(f, "free ${}", s),
            Inst::SetGlobal(s, v) => write!(f, "$global[{}] = {}", s, v),
            Inst::SetLocal(s, v) => write!(f, "${} = {}", s, v),
            Inst::Block(b) => write!(f, "{}", b),
            Inst::Func(func) => write!(f, "{}", func),
            Inst::IfBlock(b) => write!(f, "{}", b),
            Inst::Loop(l) => write!(f, "{}", l),
            Inst::Store(s) => write!(f, "{}", s),
            Inst::IncRef(v, i) => write!(f, "incref {} {}", v, i),
            Inst::DecRef(v) => write!(f, "decref {}", v),
            Inst::Return(v) => write!(f, "ret {}", v),
            Inst::MemCopy(dst, src, size) => {
                write!(f, "memcpy dst={} src={} size={}", dst, src, size)
            }
            Inst::Break => write!(f, "break"),
            Inst::Halt => write!(f, "halt"),
        }
    }
}

impl<'a> GetLocalsMut<'a> for Inst {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        match self {
            Inst::Free(i) => {
                vec![i]
            }
            Inst::SetGlobal(_, v) => v.get_locals_mut(),
            Inst::SetLocal(i, v) => {
                let mut locs = vec![i];
                locs.extend(v.get_locals_mut());
                locs
            }
            Inst::Block(b) => b.get_locals_mut(),
            Inst::Func(f) => f.get_locals_mut(),
            Inst::IfBlock(b) => b.get_locals_mut(),
            Inst::Loop(b) => b.get_locals_mut(),
            Inst::Store(s) => s.get_locals_mut(),
            Inst::MemCopy(d, s, z) => {
                let mut locs = d.get_locals_mut();
                locs.extend(s.get_locals_mut());
                locs.extend(z.get_locals_mut());
                locs
            }
            Inst::Value(v) | Inst::IncRef(v, _) | Inst::DecRef(v) | Inst::Return(v) => {
                v.get_locals_mut()
            }
            Inst::Break | Inst::Halt => vec![],
        }
    }
}

impl<'a> GetLocals<'a> for Inst {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        match self {
            Inst::Free(i) => {
                vec![i]
            }
            Inst::SetGlobal(_, v) => v.get_locals(),
            Inst::SetLocal(i, v) => {
                let mut locs = vec![i];
                locs.extend(v.get_locals());
                locs
            }
            Inst::Block(b) => b.get_locals(),
            Inst::Func(f) => f.get_locals(),
            Inst::IfBlock(b) => b.get_locals(),
            Inst::Loop(b) => b.get_locals(),
            Inst::Store(s) => s.get_locals(),
            Inst::MemCopy(d, s, z) => {
                let mut locs = d.get_locals();
                locs.extend(s.get_locals());
                locs.extend(z.get_locals());
                locs
            }
            Inst::Value(v) | Inst::IncRef(v, _) | Inst::DecRef(v) | Inst::Return(v) => {
                v.get_locals()
            }
            Inst::Break | Inst::Halt => vec![],
        }
    }
}

impl ApplySubst for Inst {
    fn apply_subst(self, subst: &Subst) -> Self {
        match self {
            Inst::Value(v) => Inst::Value(v.apply_subst(subst)),
            Inst::Free(i) => Inst::Free(i),
            Inst::SetGlobal(i, v) => Inst::SetGlobal(i, v.apply_subst(subst)),
            Inst::SetLocal(i, v) => Inst::SetLocal(i, v.apply_subst(subst)),
            Inst::Block(b) => Inst::Block(b.apply_subst(subst)),
            Inst::Func(f) => Inst::Func(f.apply_subst(subst)),
            Inst::IfBlock(b) => Inst::IfBlock(b.apply_subst(subst)),
            Inst::Loop(l) => Inst::Loop(l.apply_subst(subst)),
            Inst::Store(s) => Inst::Store(s.apply_subst(subst)),
            Inst::MemCopy(d, s, z) => Inst::MemCopy(d, s, z),
            Inst::IncRef(v, i) => Inst::IncRef(v.apply_subst(subst), i),
            Inst::DecRef(v) => Inst::DecRef(v.apply_subst(subst)),
            Inst::Return(v) => Inst::Return(v.apply_subst(subst)),
            Inst::Break => Inst::Break,
            Inst::Halt => Inst::Halt,
        }
    }
}

impl NamedInst for Inst {
    fn get_name(&self) -> &Path {
        match self {
            Inst::Value(v) => v.get_name(),
            _ => panic!("{} is unnamed", self),
        }
    }

    fn set_name(&mut self, name: Path) {
        match self {
            Inst::Value(v) => v.set_name(name),
            _ => panic!("{} is unnamed", self),
        }
    }
}

impl Inst {
    pub fn new<T>(t: T) -> Inst
    where
        T: Into<Inst>,
    {
        t.into()
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Op {
    Malloc,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitXor,
    BitAnd,
    BitOr,
    BitNot,
    ArithShiftLeft,
    ArithShiftRight,
    LogicalShiftLeft,
    LogicalShiftRight,
    RotateLeft,
    RotateRight,
    Lt,
    LtEq,
    Gt,
    GtEq,
    Eq,
    Neq,
}

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Op::Malloc => write!(f, "malloc"),
            Op::Add => write!(f, "add"),
            Op::Sub => write!(f, "sub"),
            Op::Mul => write!(f, "mul"),
            Op::Div => write!(f, "div"),
            Op::Mod => write!(f, "mod"),
            Op::BitXor => write!(f, "xor"),
            Op::BitAnd => write!(f, "bitand"),
            Op::BitOr => write!(f, "bitor"),
            Op::BitNot => write!(f, "bitnot"),
            Op::ArithShiftLeft => write!(f, "asl"),
            Op::ArithShiftRight => write!(f, "asr"),
            Op::LogicalShiftLeft => write!(f, "lsl"),
            Op::LogicalShiftRight => write!(f, "lsr"),
            Op::RotateLeft => write!(f, "rotl"),
            Op::RotateRight => write!(f, "rotr"),
            Op::Lt => write!(f, "lt"),
            Op::LtEq => write!(f, "lteq"),
            Op::Gt => write!(f, "gt"),
            Op::GtEq => write!(f, "gteq"),
            Op::Eq => write!(f, "eq"),
            Op::Neq => write!(f, "neq"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum BranchOp {
    BranchNZ,
    BranchZ,
}

impl std::fmt::Display for BranchOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BranchOp::BranchNZ => write!(f, "branchnz"),
            BranchOp::BranchZ => write!(f, "branchz"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Size {
    pub ptrs: usize,
    pub bytes: usize,
}

LirImplInto!(Atom for Size);

impl Default for Size {
    fn default() -> Size {
        Size::zero()
    }
}

impl std::ops::Add for Size {
    type Output = Size;

    fn add(self, rhs: Size) -> Size {
        Size {
            ptrs: self.ptrs + rhs.ptrs,
            bytes: self.bytes + rhs.bytes,
        }
    }
}

impl std::ops::AddAssign for Size {
    fn add_assign(&mut self, rhs: Self) {
        self.ptrs += rhs.ptrs;
        self.bytes += rhs.bytes;
    }
}

impl std::ops::Mul for Size {
    type Output = Size;

    fn mul(self, rhs: Self) -> Self::Output {
        Size {
            ptrs: self.ptrs * rhs.ptrs,
            bytes: self.bytes * rhs.bytes,
        }
    }
}

impl std::ops::Mul<usize> for Size {
    type Output = Size;

    fn mul(self, rhs: usize) -> Self::Output {
        Size {
            ptrs: self.ptrs * rhs,
            bytes: self.bytes * rhs,
        }
    }
}

impl std::ops::MulAssign for Size {
    fn mul_assign(&mut self, rhs: Self) {
        self.ptrs *= rhs.ptrs;
        self.bytes *= rhs.bytes;
    }
}

impl Sum for Size {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        let mut s = Size::default();
        for t in iter {
            s.ptrs += t.ptrs;
            s.bytes += t.bytes;
        }
        s
    }
}

impl std::fmt::Display for Size {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.ptrs == 0 && self.bytes == 0 {
            write!(f, "0")
        } else if self.ptrs == 0 {
            write!(f, "{} bytes", self.bytes)
        } else if self.bytes == 0 {
            write!(f, "{} ptrs", self.ptrs)
        } else {
            write!(f, "{} ptrs and {} bytes", self.ptrs, self.bytes)
        }
    }
}

impl Size {
    pub fn zero() -> Size {
        Size { ptrs: 0, bytes: 0 }
    }

    pub fn ptr() -> Size {
        Size { bytes: 0, ptrs: 1 }
    }

    pub fn bytes(bytes: usize) -> Size {
        Size { bytes, ptrs: 0 }
    }

    pub fn ptrs(ptrs: usize) -> Size {
        Size { bytes: 0, ptrs }
    }

    pub fn is_zero(&self) -> bool {
        self.ptrs == 0 && self.bytes == 0
    }
}

#[derive(Clone, Debug)]
pub struct Extern {
    pub name: Path,
    pub ty: Ty,
    pub is_mutable: bool,
    pub src: Option<String>,
}

impl std::fmt::Display for Extern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "extern {} : {}", self.name, self.ty)
    }
}

#[derive(Clone, Debug)]
pub struct Program {
    pub module_path: ast::Path,
    pub globals: Vec<Global>,
    pub data: Vec<Data>,
    pub funcs: Vec<Func>,
    pub externs: Vec<Extern>,
    pub extern_set: HashSet<Path>,
    pub trait_member_set: HashSet<Path>,
    pub poly_fn_map: HashMap<Path, usize>,
    pub type_metadata: HashMap<String, TypeMetadata>,
    pub module_map_idx: i64,    // data index for __module_map
    pub type_metadata_idx: i64, // data index for __type_metadata
    pub init_func: String,      // module init func
    pub start_idx: i64,         // index in Funcs for _start
    pub main_idx: i64,          // index in Funcs for main
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &join(&self.externs, "\n"))?;

        if !self.externs.is_empty() {
            write!(f, "\n\n")?;
        }

        write!(f, "{}", &join(&self.funcs, "\n\n"))
    }
}

impl Program {
    pub fn new(m: ast::Path) -> Program {
        Program {
            module_path: m,
            globals: vec![],
            data: vec![],
            funcs: vec![],
            externs: vec![],
            poly_fn_map: HashMap::new(),
            extern_set: HashSet::new(),
            trait_member_set: HashSet::new(),
            type_metadata: HashMap::new(),
            init_func: "".to_string(),
            start_idx: -1,
            main_idx: -1,
            module_map_idx: 0,
            type_metadata_idx: 0,
        }
    }

    pub fn post_process(&mut self) {
        optimize(self, 0);
    }
}

#[derive(Clone, Debug)]
pub struct Data {
    idx: usize,
    name: String,
    value: Vec<u8>,
}

impl Data {
    pub fn new(idx: usize, name: String, value: Vec<u8>) -> Data {
        Data { idx, name, value }
    }

    pub fn value(&self) -> Vec<u8> {
        self.value.clone()
    }
}

#[derive(Clone, Debug)]
pub struct Global {
    idx: usize,
    name: String,
    ty: Ty,
    size: Size,
}

#[derive(Clone, Debug)]
pub struct Local {
    pub idx: usize,
    pub ty: Ty,
    pub name: Option<String>,
}

impl std::fmt::Display for Local {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(name) = &self.name {
            write!(f, "${}", name)
        } else {
            write!(f, "${}", self.idx)
        }
    }
}

impl ApplySubst for Local {
    fn apply_subst(mut self, subst: &Subst) -> Self {
        self.ty = self.ty.apply_subst(subst);
        self
    }
}

impl<'a> GetLocalsMut<'a> for Local {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        vec![&mut self.idx]
    }
}

impl<'a> GetLocals<'a> for Local {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        vec![&self.idx]
    }
}

impl Local {
    pub fn new(idx: usize, ty: Ty) -> Local {
        Local {
            idx,
            ty,
            name: None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Param {
    pub idx: usize,
    pub name: String,
    pub ty: Ty,
    pub size: Size,
}

impl std::fmt::Display for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}: {}", self.name, self.ty)
    }
}

impl<'a> GetLocalsMut<'a> for Param {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        vec![&mut self.idx]
    }
}

impl<'a> GetLocals<'a> for Param {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        vec![&self.idx]
    }
}

impl ApplySubst for Param {
    fn apply_subst(self, subst: &Subst) -> Self {
        Param {
            idx: self.idx,
            name: self.name,
            ty: self.ty.apply_subst(subst),
            size: self.size,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Block {
    pub name: String,
    pub instructions: Vec<Node<Inst, SourceInfo>>,
}

impl std::fmt::Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", indent_lines(join(&self.instructions, "\n"), 2))
    }
}

impl<'a> GetLocalsMut<'a> for Block {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.instructions.get_locals_mut()
    }
}

impl<'a> GetLocals<'a> for Block {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.instructions.get_locals()
    }
}

impl ApplySubst for Block {
    fn apply_subst(self, subst: &Subst) -> Self {
        Block {
            name: self.name,
            instructions: self.instructions.apply_subst(subst),
        }
    }
}

impl Block {
    pub fn new() -> Block {
        Block {
            name: str!(""),
            instructions: vec![],
        }
    }
}

#[derive(Clone, Debug)]
pub struct Func {
    pub name: Path,
    pub params: Vec<Param>,
    pub locals: Vec<Local>,
    pub ty: Ty,
    pub body: Block,
    pub decorators: Option<Vec<Decorator>>,
    pub symbols: SymbolSet,
}

impl std::fmt::Display for Func {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (_, preds, _, ret_ty) = self.ty.try_borrow_fn().unwrap();
        write!(
            f,
            "fn {}({}) -> {}{} {{\n{}\n}}",
            self.name,
            map_join(&self.params, ", ", |p| format!("${}: {}", p.idx, p.ty)),
            ret_ty,
            if let Some(preds) = preds {
                format!(" where {}", join(preds, ", "))
            } else {
                str!("")
            },
            self.body
        )
    }
}

impl<'a> GetLocalsMut<'a> for Func {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        let mut locs = self.locals.get_locals_mut();
        locs.extend(self.params.get_locals_mut());
        locs.extend(self.body.get_locals_mut());
        locs
    }
}

impl<'a> GetLocals<'a> for Func {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        let mut locs = self.locals.get_locals();
        locs.extend(self.params.get_locals());
        locs.extend(self.body.get_locals());
        locs
    }
}

impl ApplySubst for Func {
    fn apply_subst(self, subst: &Subst) -> Func {
        Func {
            name: self.name,
            params: self.params.apply_subst(subst),
            locals: self.locals.apply_subst(subst),
            ty: self.ty.apply_subst(subst),
            body: self.body.apply_subst(subst),
            decorators: self.decorators,
            symbols: self.symbols.apply_subst(subst),
        }
    }
}

impl Func {
    pub fn new(name: Path, ty: Ty) -> Func {
        Func {
            name,
            ty,
            params: vec![],
            locals: vec![],
            body: Block::new(),
            decorators: None,
            symbols: SymbolSet::new(),
        }
    }

    pub fn has_decorator(&self, p: &Path) -> bool {
        self.decorators
            .as_ref()
            .map(|v| v.iter().any(|d| d.path.path() == p))
            .unwrap_or_default()
    }

    pub fn has_inline(&self) -> bool {
        let path = Path::from("inline");
        self.has_decorator(&path)
    }

    pub fn inline(
        mut self,
        args: Vec<Variable>,
        info: SourceInfo,
        offset: usize,
    ) -> (Vec<Local>, Vec<Node<Inst, SourceInfo>>, Value) {
        self.offset_locals(offset);

        let mut insts = self
            .params
            .iter()
            .zip(args.into_iter())
            .map(|(p, a)| Node::new(Inst::SetLocal(p.idx, Atom::new(a).into()), info.clone()))
            .collect::<Vec<_>>();

        insts.extend(self.body.instructions);
        let last = insts.pop();
        let ret_val = if let Some(Node {
            value: Inst::Return(v),
            ..
        }) = last
        {
            v
        } else {
            if let Some(last) = last {
                insts.push(last);
            }
            Value::Empty
        };
        (self.locals, insts, ret_val)
    }
}

#[derive(Clone, Debug)]
pub struct FuncRef {
    pub name: String,
    pub ty: Ty,
}

impl std::fmt::Display for FuncRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "$fn[{}]", self.name)
    }
}

impl ApplySubst for FuncRef {
    fn apply_subst(self, subst: &Subst) -> Self {
        FuncRef {
            name: self.name,
            ty: self.ty.apply_subst(subst),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Call {
    pub fn_name: Path,
    pub original_fn: Path,
    pub fn_ref: Option<usize>,
    pub args: Vec<Variable>,
    pub ty: Ty,
    pub poly_ty: Option<Ty>,
}

LirImplInto!(Value for Call);

impl std::fmt::Display for Call {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", self.fn_name, join(&self.args, ", "))
    }
}

impl<'a> GetLocalsMut<'a> for Call {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.args.get_locals_mut()
    }
}

impl<'a> GetLocals<'a> for Call {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.args.get_locals()
    }
}

impl ApplySubst for Call {
    fn apply_subst(self, subst: &Subst) -> Self {
        Call {
            fn_name: self.fn_name.apply_subst(subst),
            original_fn: self.original_fn,
            fn_ref: self.fn_ref,
            args: self.args.apply_subst(subst),
            ty: self.ty.apply_subst(subst),
            poly_ty: self.poly_ty,
        }
    }
}

impl NamedInst for Call {
    fn get_name(&self) -> &Path {
        &self.fn_name
    }

    fn set_name(&mut self, name: Path) {
        self.fn_name = name;
    }
}

impl Call {
    pub fn new(fn_name: Path, args: Vec<Variable>, ty: Ty, poly_ty: Option<Ty>) -> Value {
        Value::Call(Call {
            original_fn: fn_name.clone(),
            fn_ref: None,
            ty,
            poly_ty,
            args,
            fn_name,
        })
    }

    pub fn new_ref(fn_ref: usize, args: Vec<Variable>, ty: Ty, poly_ty: Option<Ty>) -> Value {
        Value::Call(Call {
            original_fn: Path::new(),
            fn_name: Path::new(),
            fn_ref: Some(fn_ref),
            ty,
            poly_ty,
            args,
        })
    }
}

#[derive(Clone, Debug)]
pub struct CExternCall {
    fn_name: String,
    args: Vec<Atom>,
    ty: Ty,
}

LirImplInto!(Value for CExternCall);

impl std::fmt::Display for CExternCall {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@extern {}({})", self.fn_name, join(&self.args, ", "))
    }
}

impl<'a> GetLocalsMut<'a> for CExternCall {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.args.get_locals_mut()
    }
}

impl<'a> GetLocals<'a> for CExternCall {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.args.get_locals()
    }
}

#[derive(Clone, Debug)]
pub struct IfBlock {
    pub name: String,
    pub cond: Block,
    pub then: Block,
    pub els: Block,
    pub end: Block,
}

impl std::fmt::Display for IfBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(if (\n{}) then: (\n{}) else: (\n{}) end: (\n{})\n)",
            indent_lines(&self.cond, 2),
            indent_lines(&self.then, 2),
            indent_lines(&self.els, 2),
            indent_lines(&self.end, 2)
        )
    }
}

impl<'a> GetLocalsMut<'a> for IfBlock {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        let mut locs = self.cond.get_locals_mut();
        locs.extend(self.then.get_locals_mut());
        locs.extend(self.els.get_locals_mut());
        locs.extend(self.end.get_locals_mut());
        locs
    }
}

impl<'a> GetLocals<'a> for IfBlock {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        let mut locs = self.cond.get_locals();
        locs.extend(self.then.get_locals());
        locs.extend(self.els.get_locals());
        locs.extend(self.end.get_locals());
        locs
    }
}

impl ApplySubst for IfBlock {
    fn apply_subst(self, subst: &Subst) -> Self {
        IfBlock {
            name: self.name,
            cond: self.cond.apply_subst(subst),
            then: self.then.apply_subst(subst),
            els: self.els.apply_subst(subst),
            end: self.end.apply_subst(subst),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Loop {
    pub name: String,
    pub begin: Block,
    pub cond: Block,
    pub body: Block,
    pub end: Block,
}

impl<'a> GetLocalsMut<'a> for Loop {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        let mut locs = self.begin.get_locals_mut();
        locs.extend(self.cond.get_locals_mut());
        locs.extend(self.body.get_locals_mut());
        locs.extend(self.end.get_locals_mut());
        locs
    }
}

impl<'a> GetLocals<'a> for Loop {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        let mut locs = self.begin.get_locals();
        locs.extend(self.cond.get_locals());
        locs.extend(self.body.get_locals());
        locs.extend(self.end.get_locals());
        locs
    }
}

impl ApplySubst for Loop {
    fn apply_subst(self, subst: &Subst) -> Self {
        Loop {
            name: self.name,
            begin: self.begin.apply_subst(subst),
            cond: self.cond.apply_subst(subst),
            body: self.body.apply_subst(subst),
            end: self.end.apply_subst(subst),
        }
    }
}

impl std::fmt::Display for Loop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(loop begin: (\n{}) cond: (\n{}) body: (\n{}) end: (\n{})\n)",
            indent_lines(&self.begin, 2),
            indent_lines(&self.cond, 2),
            indent_lines(&self.body, 2),
            indent_lines(&self.end, 2)
        )
    }
}

#[derive(Clone, Debug)]
pub struct Branch {
    op: BranchOp,
    operand: Atom,
    then_label: String,
    else_label: String,
}

LirImplInto!(Value for Branch);

impl std::fmt::Display for Branch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {} {} {}",
            self.op, self.operand, self.then_label, self.else_label
        )
    }
}

impl<'a> GetLocalsMut<'a> for Branch {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.operand.get_locals_mut()
    }
}

impl<'a> GetLocals<'a> for Branch {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.operand.get_locals()
    }
}

impl ApplySubst for Branch {
    fn apply_subst(self, subst: &Subst) -> Self {
        Branch {
            op: self.op,
            operand: self.operand.apply_subst(subst),
            then_label: self.then_label,
            else_label: self.else_label,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Select {
    cond: Variable,
    then: Atom,
    els: Atom,
}

LirImplInto!(Value for Select);

impl std::fmt::Display for Select {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "select {} {} {}", self.cond, self.then, self.els)
    }
}

impl<'a> GetLocalsMut<'a> for Select {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        let mut loc = self.cond.get_locals_mut();
        loc.extend(self.then.get_locals_mut());
        loc.extend(self.els.get_locals_mut());
        loc
    }
}

impl<'a> GetLocals<'a> for Select {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        let mut loc = self.cond.get_locals();
        loc.extend(self.then.get_locals());
        loc.extend(self.els.get_locals());
        loc
    }
}

impl ApplySubst for Select {
    fn apply_subst(self, subst: &Subst) -> Self {
        Select {
            cond: self.cond.apply_subst(subst),
            then: self.then.apply_subst(subst),
            els: self.els.apply_subst(subst),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Store {
    pub dst: Variable,
    pub value: Value,
    pub offset: Size,
    pub size: Size,
}

impl std::fmt::Display for Store {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "store {} {} offset=({}) size=({})",
            self.dst, self.value, self.offset, self.size
        )
    }
}

impl<'a> GetLocalsMut<'a> for Store {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        let mut locs = self.dst.get_locals_mut();
        locs.extend(self.value.get_locals_mut());
        locs
    }
}

impl<'a> GetLocals<'a> for Store {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        let mut locs = self.dst.get_locals();
        locs.extend(self.value.get_locals());
        locs
    }
}

impl ApplySubst for Store {
    fn apply_subst(self, subst: &Subst) -> Self {
        Store {
            dst: self.dst.apply_subst(subst),
            value: self.value.apply_subst(subst),
            offset: self.offset,
            size: self.size,
        }
    }
}

impl Store {
    pub fn new(dst: Variable, value: Value, offset: Size, size: Size) -> Inst {
        Inst::Store(Store {
            dst,
            value,
            offset,
            size,
        })
    }
}

#[derive(Clone, Debug)]
pub struct Load {
    pub src: Variable,
    pub offset: Size,
    pub size: Size,
}

LirImplInto!(Value for Load);

impl std::fmt::Display for Load {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "load {} offset=({}) size=({})",
            self.src, self.offset, self.size
        )
    }
}

impl<'a> GetLocalsMut<'a> for Load {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.src.get_locals_mut()
    }
}

impl<'a> GetLocals<'a> for Load {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.src.get_locals()
    }
}

impl ApplySubst for Load {
    fn apply_subst(self, subst: &Subst) -> Self {
        Load {
            src: self.src.apply_subst(subst),
            offset: self.offset,
            size: self.size,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Lea {
    value: Atom,
    src_offset: Size,
    dst_offset: Size,
}

LirImplInto!(Value for Lea);

impl std::fmt::Display for Lea {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "lea {} {} {}",
            self.value, self.src_offset, self.dst_offset,
        )
    }
}

impl<'a> GetLocalsMut<'a> for Lea {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.value.get_locals_mut()
    }
}

impl<'a> GetLocals<'a> for Lea {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.value.get_locals()
    }
}

impl ApplySubst for Lea {
    fn apply_subst(self, subst: &Subst) -> Self {
        Lea {
            value: self.value.apply_subst(subst),
            src_offset: self.src_offset,
            dst_offset: self.dst_offset,
        }
    }
}

#[derive(Clone, Debug)]
pub struct GetField {
    pub src: Variable,
    pub field: String,
}

LirImplInto!(Value for GetField);

impl std::fmt::Display for GetField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "getfield {} {}", self.src, self.field)
    }
}

impl<'a> GetLocalsMut<'a> for GetField {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.src.get_locals_mut()
    }
}

impl<'a> GetLocals<'a> for GetField {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.src.get_locals()
    }
}

impl ApplySubst for GetField {
    fn apply_subst(self, subst: &Subst) -> Self {
        GetField {
            src: self.src.apply_subst(subst),
            field: self.field,
        }
    }
}

#[derive(Clone, Debug)]
pub struct BasicOp {
    pub op: Op,
    pub size: Size,
    pub signed: bool,
    pub operands: Vec<Atom>,
}

LirImplInto!(Value for BasicOp);

impl std::fmt::Display for BasicOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let operands = join(&self.operands, " ");
        let ext = match (self.signed, self.size.ptrs, self.size.bytes) {
            (true, 1, _) => "int",
            (false, 1, _) => "uint",
            (true, _, 1) => "i8",
            (true, _, 2) => "i16",
            (true, _, 4) => "i32",
            (true, _, 8) => "i64",
            (false, _, 1) => "i8",
            (false, _, 2) => "i16",
            (false, _, 4) => "i32",
            (false, _, 8) => "i64",
            _ => panic!("invalid size for binop: {}", self.size),
        };

        write!(f, "{}.{} {}", self.op, ext, operands)
    }
}

impl<'a> GetLocalsMut<'a> for BasicOp {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.operands.get_locals_mut()
    }
}

impl<'a> GetLocals<'a> for BasicOp {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.operands.get_locals()
    }
}

impl ApplySubst for BasicOp {
    fn apply_subst(self, subst: &Subst) -> Self {
        BasicOp {
            op: self.op,
            size: self.size,
            signed: self.signed,
            operands: self.operands.apply_subst(subst),
        }
    }
}

impl From<AsmOp> for BasicOp {
    fn from(op: AsmOp) -> Self {
        match op {
            AsmOp::Malloc => unreachable!(),
            AsmOp::ISizeEq => BasicOp {
                op: Op::Eq,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Eq => BasicOp {
                op: Op::Eq,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Eq => BasicOp {
                op: Op::Eq,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Eq => BasicOp {
                op: Op::Eq,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Eq => BasicOp {
                op: Op::Eq,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeEq => BasicOp {
                op: Op::Eq,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Eq => BasicOp {
                op: Op::Eq,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Eq => BasicOp {
                op: Op::Eq,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Eq => BasicOp {
                op: Op::Eq,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Eq => BasicOp {
                op: Op::Eq,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeNeq => BasicOp {
                op: Op::Neq,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Neq => BasicOp {
                op: Op::Neq,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Neq => BasicOp {
                op: Op::Neq,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Neq => BasicOp {
                op: Op::Neq,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Neq => BasicOp {
                op: Op::Neq,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeNeq => BasicOp {
                op: Op::Neq,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Neq => BasicOp {
                op: Op::Neq,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Neq => BasicOp {
                op: Op::Neq,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Neq => BasicOp {
                op: Op::Neq,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Neq => BasicOp {
                op: Op::Neq,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeAdd => BasicOp {
                op: Op::Add,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Add => BasicOp {
                op: Op::Add,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Add => BasicOp {
                op: Op::Add,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Add => BasicOp {
                op: Op::Add,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Add => BasicOp {
                op: Op::Add,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeAdd => BasicOp {
                op: Op::Add,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Add => BasicOp {
                op: Op::Add,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Add => BasicOp {
                op: Op::Add,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Add => BasicOp {
                op: Op::Add,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Add => BasicOp {
                op: Op::Add,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeSub => BasicOp {
                op: Op::Sub,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Sub => BasicOp {
                op: Op::Sub,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Sub => BasicOp {
                op: Op::Sub,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Sub => BasicOp {
                op: Op::Sub,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Sub => BasicOp {
                op: Op::Sub,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeSub => BasicOp {
                op: Op::Sub,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Sub => BasicOp {
                op: Op::Sub,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Sub => BasicOp {
                op: Op::Sub,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Sub => BasicOp {
                op: Op::Sub,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Sub => BasicOp {
                op: Op::Sub,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeMul => BasicOp {
                op: Op::Mul,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Mul => BasicOp {
                op: Op::Mul,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Mul => BasicOp {
                op: Op::Mul,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Mul => BasicOp {
                op: Op::Mul,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Mul => BasicOp {
                op: Op::Mul,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeMul => BasicOp {
                op: Op::Mul,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Mul => BasicOp {
                op: Op::Mul,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Mul => BasicOp {
                op: Op::Mul,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Mul => BasicOp {
                op: Op::Mul,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Mul => BasicOp {
                op: Op::Mul,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeDiv => BasicOp {
                op: Op::Div,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Div => BasicOp {
                op: Op::Div,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Div => BasicOp {
                op: Op::Div,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Div => BasicOp {
                op: Op::Div,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Div => BasicOp {
                op: Op::Div,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeDiv => BasicOp {
                op: Op::Div,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Div => BasicOp {
                op: Op::Div,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Div => BasicOp {
                op: Op::Div,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Div => BasicOp {
                op: Op::Div,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Div => BasicOp {
                op: Op::Div,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeMod => BasicOp {
                op: Op::Mod,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Mod => BasicOp {
                op: Op::Mod,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Mod => BasicOp {
                op: Op::Mod,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Mod => BasicOp {
                op: Op::Mod,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Mod => BasicOp {
                op: Op::Mod,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeMod => BasicOp {
                op: Op::Mod,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Mod => BasicOp {
                op: Op::Mod,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Mod => BasicOp {
                op: Op::Mod,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Mod => BasicOp {
                op: Op::Mod,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Mod => BasicOp {
                op: Op::Mod,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeAnd => BasicOp {
                op: Op::BitAnd,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8And => BasicOp {
                op: Op::BitAnd,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16And => BasicOp {
                op: Op::BitAnd,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32And => BasicOp {
                op: Op::BitAnd,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64And => BasicOp {
                op: Op::BitAnd,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeAnd => BasicOp {
                op: Op::BitAnd,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8And => BasicOp {
                op: Op::BitAnd,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16And => BasicOp {
                op: Op::BitAnd,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32And => BasicOp {
                op: Op::BitAnd,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64And => BasicOp {
                op: Op::BitAnd,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeOr => BasicOp {
                op: Op::BitOr,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Or => BasicOp {
                op: Op::BitOr,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Or => BasicOp {
                op: Op::BitOr,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Or => BasicOp {
                op: Op::BitOr,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Or => BasicOp {
                op: Op::BitOr,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeOr => BasicOp {
                op: Op::BitOr,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Or => BasicOp {
                op: Op::BitOr,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Or => BasicOp {
                op: Op::BitOr,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Or => BasicOp {
                op: Op::BitOr,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Or => BasicOp {
                op: Op::BitOr,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeXor => BasicOp {
                op: Op::BitXor,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Xor => BasicOp {
                op: Op::BitXor,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Xor => BasicOp {
                op: Op::BitXor,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Xor => BasicOp {
                op: Op::BitXor,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Xor => BasicOp {
                op: Op::BitXor,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeXor => BasicOp {
                op: Op::BitXor,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Xor => BasicOp {
                op: Op::BitXor,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Xor => BasicOp {
                op: Op::BitXor,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Xor => BasicOp {
                op: Op::BitXor,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Xor => BasicOp {
                op: Op::BitXor,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeLt => BasicOp {
                op: Op::Lt,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Lt => BasicOp {
                op: Op::Lt,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Lt => BasicOp {
                op: Op::Lt,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Lt => BasicOp {
                op: Op::Lt,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Lt => BasicOp {
                op: Op::Lt,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeLt => BasicOp {
                op: Op::Lt,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Lt => BasicOp {
                op: Op::Lt,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Lt => BasicOp {
                op: Op::Lt,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Lt => BasicOp {
                op: Op::Lt,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Lt => BasicOp {
                op: Op::Lt,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeGt => BasicOp {
                op: Op::Gt,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Gt => BasicOp {
                op: Op::Gt,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Gt => BasicOp {
                op: Op::Gt,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Gt => BasicOp {
                op: Op::Gt,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Gt => BasicOp {
                op: Op::Gt,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeGt => BasicOp {
                op: Op::Gt,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Gt => BasicOp {
                op: Op::Gt,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Gt => BasicOp {
                op: Op::Gt,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Gt => BasicOp {
                op: Op::Gt,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Gt => BasicOp {
                op: Op::Gt,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeLtEq => BasicOp {
                op: Op::LtEq,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8LtEq => BasicOp {
                op: Op::LtEq,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16LtEq => BasicOp {
                op: Op::LtEq,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32LtEq => BasicOp {
                op: Op::LtEq,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64LtEq => BasicOp {
                op: Op::LtEq,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeLtEq => BasicOp {
                op: Op::LtEq,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8LtEq => BasicOp {
                op: Op::LtEq,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16LtEq => BasicOp {
                op: Op::LtEq,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32LtEq => BasicOp {
                op: Op::LtEq,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64LtEq => BasicOp {
                op: Op::LtEq,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeGtEq => BasicOp {
                op: Op::GtEq,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8GtEq => BasicOp {
                op: Op::GtEq,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16GtEq => BasicOp {
                op: Op::GtEq,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32GtEq => BasicOp {
                op: Op::GtEq,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64GtEq => BasicOp {
                op: Op::GtEq,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeGtEq => BasicOp {
                op: Op::GtEq,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8GtEq => BasicOp {
                op: Op::GtEq,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16GtEq => BasicOp {
                op: Op::GtEq,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32GtEq => BasicOp {
                op: Op::GtEq,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64GtEq => BasicOp {
                op: Op::GtEq,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeShl => BasicOp {
                op: Op::ArithShiftLeft,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Shl => BasicOp {
                op: Op::ArithShiftLeft,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Shl => BasicOp {
                op: Op::ArithShiftLeft,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Shl => BasicOp {
                op: Op::ArithShiftLeft,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Shl => BasicOp {
                op: Op::ArithShiftLeft,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeShl => BasicOp {
                op: Op::ArithShiftLeft,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Shl => BasicOp {
                op: Op::ArithShiftLeft,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Shl => BasicOp {
                op: Op::ArithShiftLeft,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Shl => BasicOp {
                op: Op::ArithShiftLeft,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Shl => BasicOp {
                op: Op::ArithShiftLeft,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeShr => BasicOp {
                op: Op::ArithShiftRight,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Shr => BasicOp {
                op: Op::ArithShiftRight,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Shr => BasicOp {
                op: Op::ArithShiftRight,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Shr => BasicOp {
                op: Op::ArithShiftRight,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Shr => BasicOp {
                op: Op::ArithShiftRight,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeShr => BasicOp {
                op: Op::ArithShiftRight,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Shr => BasicOp {
                op: Op::ArithShiftRight,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Shr => BasicOp {
                op: Op::ArithShiftRight,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Shr => BasicOp {
                op: Op::ArithShiftRight,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Shr => BasicOp {
                op: Op::ArithShiftRight,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeRotl => BasicOp {
                op: Op::RotateLeft,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Rotl => BasicOp {
                op: Op::RotateLeft,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Rotl => BasicOp {
                op: Op::RotateLeft,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Rotl => BasicOp {
                op: Op::RotateLeft,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Rotl => BasicOp {
                op: Op::RotateLeft,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeRotl => BasicOp {
                op: Op::RotateLeft,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Rotl => BasicOp {
                op: Op::RotateLeft,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Rotl => BasicOp {
                op: Op::RotateLeft,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Rotl => BasicOp {
                op: Op::RotateLeft,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Rotl => BasicOp {
                op: Op::RotateLeft,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            AsmOp::ISizeRotr => BasicOp {
                op: Op::RotateRight,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            AsmOp::I8Rotr => BasicOp {
                op: Op::RotateRight,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            AsmOp::I16Rotr => BasicOp {
                op: Op::RotateRight,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            AsmOp::I32Rotr => BasicOp {
                op: Op::RotateRight,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            AsmOp::I64Rotr => BasicOp {
                op: Op::RotateRight,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            AsmOp::USizeRotr => BasicOp {
                op: Op::RotateRight,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            AsmOp::U8Rotr => BasicOp {
                op: Op::RotateRight,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            AsmOp::U16Rotr => BasicOp {
                op: Op::RotateRight,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            AsmOp::U32Rotr => BasicOp {
                op: Op::RotateRight,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            AsmOp::U64Rotr => BasicOp {
                op: Op::RotateRight,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct IntConvert {
    value: Atom,
    src: (Size, bool),
    dst: (Size, bool),
}

LirImplInto!(Value for IntConvert);

impl std::fmt::Display for IntConvert {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} as {} {}",
            self.value,
            if self.dst.1 { "signed" } else { "unsigned" },
            self.dst.0
        )
    }
}

impl ApplySubst for IntConvert {
    fn apply_subst(self, subst: &Subst) -> Self {
        IntConvert {
            value: self.value.apply_subst(subst),
            src: self.src,
            dst: self.dst,
        }
    }
}

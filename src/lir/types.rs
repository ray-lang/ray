use crate::{
    ast::{self, Node, Path, SourceInfo},
    strutils::indent_lines,
    sym,
    typing::{
        predicate::TyPredicate,
        ty::{Ty, TyVar},
        ApplySubst, Subst,
    },
    utils::{join, map_join},
};

use std::{
    cell::{RefCell, RefMut},
    collections::{HashMap, HashSet},
};

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
    fn get_name(&self) -> &String;
    fn set_name(&mut self, name: String);
}

#[derive(Clone, Debug)]
pub struct SymbolSet;

impl SymbolSet {
    pub fn new() -> SymbolSet {
        SymbolSet {}
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

impl ApplySubst for Variable {
    fn apply_subst(self, subst: &Subst) -> Self {
        self
    }
}

#[derive(Clone, Debug)]
pub enum Atom {
    Variable(Variable),
    FuncRef(FuncRef),
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
            Atom::UintConst(u, _) => write!(f, "{}", u),
            Atom::IntConst(i, _) => write!(f, "{}", i),
            Atom::FloatConst(c, _) => write!(f, "{}", c),
            Atom::RawString(s) => write!(f, "{:?}", s),
            Atom::NilConst => write!(f, "nil"),
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

#[derive(Clone, Debug)]
pub struct Malloc(pub Size);
LirImplInto!(Value for Malloc);

impl std::fmt::Display for Malloc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "malloc({})", self.0)
    }
}

impl ApplySubst for Malloc {
    fn apply_subst(self, subst: &Subst) -> Self {
        self
    }
}

#[derive(Clone, Debug)]
pub struct Alloca(pub Size);
LirImplInto!(Value for Alloca);

impl std::fmt::Display for Alloca {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "alloca({})", self.0)
    }
}

impl ApplySubst for Alloca {
    fn apply_subst(self, subst: &Subst) -> Self {
        self
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Empty,
    Atom(Atom),
    Malloc(Malloc),
    Alloca(Alloca),
    Call(Call),
    CExternCall(CExternCall),
    Branch(Branch),
    Select(Select),
    Load(Load),
    Lea(Lea),
    BinOp(BinOp),
    IntConvert(IntConvert),
}

LirImplInto!(Inst for Value);

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Empty => write!(f, ""),
            Value::Atom(a) => write!(f, "{}", a),
            Value::Malloc(a) => write!(f, "{}", a),
            Value::Alloca(a) => write!(f, "{}", a),
            Value::Call(a) => write!(f, "{}", a),
            Value::CExternCall(a) => write!(f, "{}", a),
            Value::Branch(a) => write!(f, "{}", a),
            Value::Select(a) => write!(f, "{}", a),
            Value::Load(a) => write!(f, "{}", a),
            Value::Lea(a) => write!(f, "{}", a),
            Value::BinOp(a) => write!(f, "{}", a),
            Value::IntConvert(a) => write!(f, "{}", a),
        }
    }
}

impl ApplySubst for Value {
    fn apply_subst(self, subst: &Subst) -> Value {
        match self {
            Value::Empty => Value::Empty,
            Value::Atom(a) => Value::Atom(a.apply_subst(subst)),
            Value::Malloc(m) => Value::Malloc(m.apply_subst(subst)),
            Value::Alloca(a) => Value::Alloca(a.apply_subst(subst)),
            Value::Call(c) => Value::Call(c.apply_subst(subst)),
            Value::CExternCall(_) => todo!(),
            Value::Branch(b) => Value::Branch(b.apply_subst(subst)),
            Value::Select(s) => Value::Select(s.apply_subst(subst)),
            Value::Load(l) => Value::Load(l.apply_subst(subst)),
            Value::Lea(l) => Value::Lea(l.apply_subst(subst)),
            Value::BinOp(b) => Value::BinOp(b.apply_subst(subst)),
            Value::IntConvert(i) => Value::IntConvert(i.apply_subst(subst)),
        }
    }
}

impl NamedInst for Value {
    fn get_name(&self) -> &String {
        match self {
            Value::Call(c) => &c.fn_name,
            _ => panic!("{} is unnamed", self),
        }
    }

    fn set_name(&mut self, name: String) {
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

pub struct LirInfo {
    src: SourceInfo,
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
            Inst::Break => write!(f, "break"),
            Inst::Halt => write!(f, "halt"),
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
            Inst::IncRef(v, i) => Inst::IncRef(v.apply_subst(subst), i),
            Inst::DecRef(v) => Inst::DecRef(v.apply_subst(subst)),
            Inst::Return(v) => Inst::Return(v.apply_subst(subst)),
            Inst::Break => Inst::Break,
            Inst::Halt => Inst::Halt,
        }
    }
}

impl NamedInst for Inst {
    fn get_name(&self) -> &String {
        match self {
            Inst::Value(v) => v.get_name(),
            _ => panic!("{} is unnamed", self),
        }
    }

    fn set_name(&mut self, name: String) {
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

#[derive(Clone, Debug)]
pub enum Op {
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
    pub ptrs: u64,
    pub bytes: u64,
}

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

impl std::fmt::Display for Size {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.ptrs == 0 && self.bytes == 0 {
            write!(f, "<ZERO>")
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

    pub fn bytes(bytes: u64) -> Size {
        Size { bytes, ptrs: 0 }
    }

    pub fn ptrs(ptrs: u64) -> Size {
        Size { bytes: 0, ptrs }
    }
}

#[derive(Clone, Debug)]
pub struct Extern {
    pub name: String,
    pub ty: Ty,
    pub is_c: bool,
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
    pub extern_set: HashSet<String>,
    pub poly_fn_map: HashMap<String, usize>,
    pub defined_symbols: HashSet<sym::Symbol>,
    pub undefined_symbols: HashSet<sym::Symbol>,
    pub type_metadata: HashMap<String, TypeMetadata>,
    pub module_map_idx: i64,    // data index for __module_map
    pub type_metadata_idx: i64, // data index for __type_metadata
    pub init_func: String,      // module init func
    pub main: i64,              // index in Funcs for main
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
            defined_symbols: HashSet::new(),
            undefined_symbols: HashSet::new(),
            type_metadata: HashMap::new(),
            init_func: "".to_string(),
            main: -1,
            module_map_idx: 0,
            type_metadata_idx: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Data {
    idx: usize,
    name: String,
    initial_value: Vec<i8>,
    ty: Ty,
    size: Size,
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
    pub name: String,
    pub scope: Path,
    pub params: Vec<Param>,
    pub locals: Vec<Local>,
    pub ty: Ty,
    pub body: Block,
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

impl ApplySubst for Func {
    fn apply_subst(self, subst: &Subst) -> Func {
        Func {
            name: self.name,
            scope: self.scope,
            params: self.params.apply_subst(subst),
            locals: self.locals,
            ty: self.ty.apply_subst(subst),
            body: self.body.apply_subst(subst),
            symbols: self.symbols,
        }
    }
}

impl Func {
    pub fn new<S: Into<String>>(name: S, scope: Path, ty: Ty) -> Func {
        let name = name.into();
        log::debug!("type of {}: {}", name, ty);
        Func {
            name,
            scope,
            ty,
            params: vec![],
            locals: vec![],
            body: Block::new(),
            symbols: SymbolSet::new(),
        }
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
    pub fn_name: String,
    pub original_fn: String,
    pub fn_ref: Option<usize>,
    pub args: Vec<Atom>,
    pub ty: Ty,
    pub poly_ty: Option<Ty>,
}

LirImplInto!(Value for Call);

impl std::fmt::Display for Call {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", self.fn_name, join(&self.args, ", "))
    }
}

impl ApplySubst for Call {
    fn apply_subst(self, subst: &Subst) -> Self {
        Call {
            fn_name: self.fn_name,
            original_fn: self.original_fn,
            fn_ref: self.fn_ref,
            args: self.args.apply_subst(subst),
            ty: self.ty.apply_subst(subst),
            poly_ty: self.poly_ty,
        }
    }
}

impl NamedInst for Call {
    fn get_name(&self) -> &String {
        &self.fn_name
    }

    fn set_name(&mut self, name: String) {
        self.fn_name = name;
    }
}

impl Call {
    pub fn new(fn_name: String, args: Vec<Atom>, ty: Ty, poly_ty: Option<Ty>) -> Value {
        Value::Call(Call {
            original_fn: fn_name.clone(),
            fn_ref: None,
            ty,
            poly_ty,
            args,
            fn_name,
        })
    }

    pub fn new_ref(fn_ref: usize, args: Vec<Atom>, ty: Ty, poly_ty: Option<Ty>) -> Value {
        Value::Call(Call {
            original_fn: str!(""),
            fn_name: str!(""),
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
            "store {} {} {} {}",
            self.dst, self.value, self.offset, self.size
        )
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

#[derive(Clone, Debug)]
pub struct Load {
    pub src: Variable,
    pub offset: Size,
    pub size: Size,
}

LirImplInto!(Value for Load);

impl std::fmt::Display for Load {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "load {} {} {}", self.src, self.offset, self.size)
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
pub struct BinOp {
    op: Op,
    size: Size,
    signed: bool,
    operands: Vec<Atom>,
}

LirImplInto!(Value for BinOp);

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.op, join(&self.operands, ", "))
    }
}

impl ApplySubst for BinOp {
    fn apply_subst(self, subst: &Subst) -> Self {
        BinOp {
            op: self.op,
            size: self.size,
            signed: self.signed,
            operands: self.operands.apply_subst(subst),
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

use crate::{
    ast,
    strutils::indent_lines,
    sym,
    typing::{
        predicate::TyPredicate,
        ty::{Ty, TyVar},
    },
    utils::join,
};

use std::collections::{HashMap, HashSet};

macro_rules! LirImplInto {
    ($dst:ident for $src:ident) => {
        impl Into<$dst> for $src {
            fn into(self) -> $dst {
                $dst::$src(self)
            }
        }
    };
}

#[derive(Clone, Debug)]
pub struct FunctionType {
    ty_params: Option<Vec<TyVar>>,
    predicates: Vec<TyPredicate>,
    param_tys: Vec<Ty>,
    ret_ty: Ty,
}

impl From<Ty> for FunctionType {
    fn from(t: Ty) -> FunctionType {
        let (ty_params, predicates, param_tys, ret_ty) =
            t.try_unpack_fn().expect("expected function type");
        FunctionType {
            ty_params,
            predicates,
            param_tys,
            ret_ty,
        }
    }
}

impl std::fmt::Display for FunctionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let all = if let Some(ty_params) = &self.ty_params {
            format!("All[{}]", join(ty_params, ", "))
        } else {
            str!("")
        };

        let q = if self.predicates.len() != 0 {
            format!(" where {}", join(&self.predicates, ", "))
        } else {
            str!("")
        };
        write!(
            f,
            "{}({}) -> {}{}",
            all,
            join(&self.param_tys, ", "),
            self.ret_ty,
            q
        )
    }
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

LirImplInto!(Value for Atom);

#[derive(Clone, Debug)]
pub struct Malloc(pub Size);
LirImplInto!(Value for Malloc);

impl std::fmt::Display for Malloc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "malloc({})", self.0)
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

#[derive(Clone, Debug)]
pub enum Value {
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

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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

impl Value {
    pub fn new<V>(v: V) -> Value
    where
        V: Into<Value>,
    {
        v.into()
    }
}

#[derive(Clone, Debug)]
pub enum InstKind {
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

impl std::fmt::Display for InstKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstKind::Value(v) => write!(f, "{}", v),
            InstKind::Free(s) => write!(f, "free ${}", s),
            InstKind::SetGlobal(s, v) => write!(f, "$global[{}] = {}", s, v),
            InstKind::SetLocal(s, v) => write!(f, "${} = {}", s, v),
            InstKind::Block(b) => write!(f, "{}", b),
            InstKind::Func(func) => write!(f, "{}", func),
            InstKind::IfBlock(b) => write!(f, "{}", b),
            InstKind::Loop(l) => write!(f, "{}", l),
            InstKind::Store(s) => write!(f, "{}", s),
            InstKind::IncRef(v, i) => write!(f, "incref {} {}", v, i),
            InstKind::DecRef(v) => write!(f, "decref {}", v),
            InstKind::Return(v) => write!(f, "ret {}", v),
            InstKind::Break => write!(f, "break"),
            InstKind::Halt => write!(f, "halt"),
        }
    }
}

impl Into<Inst> for InstKind {
    fn into(self) -> Inst {
        Inst {
            kind: self,
            comment: String::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Inst {
    pub kind: InstKind,
    pub comment: String,
}

impl std::fmt::Display for Inst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            self.kind,
            if !self.comment.is_empty() {
                format!("; {}", self.comment)
            } else {
                str!("")
            }
        )
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
    name: String,
    ty: FunctionType,
    is_c: bool,
}

#[derive(Clone, Debug)]
pub struct PolyFuncRef {
    name: String,              // this is the "simple" func name
    func_ctx: String,          // the name of the enclosing function
    poly_type: FunctionType,   // the polymorphic type
    callee_type: FunctionType, // the type of the callee (which may be polymorphic as well)
}

#[derive(Clone, Debug)]
pub struct Program {
    pub module_path: ast::Path,
    pub globals: Vec<Global>,
    pub data: Vec<Data>,
    pub funcs: Vec<Func>,
    pub externs: Vec<Extern>,
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
        f.write_str(&join(&self.funcs, "\n "))
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
    // pub name: String,
    pub ty: Ty,
    // pub is_alloca: bool,
    // size: Size,
    // signed: bool,
}

impl std::fmt::Display for Local {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.idx)
    }
}

impl Local {
    pub fn new(idx: usize, ty: Ty) -> Local {
        Local {
            idx,
            ty,
            // name: String::new(),
            // is_alloca: false,
        }
    }
}

// impl Local {
//     pub fn set_type(&self, ty: typing::Ty) {
//         // self.size = getTypeSize(ty);
//         // self.signed = getTypeSign(ty);
//         self.ty = ty
//     }
// }

#[derive(Clone, Debug)]
pub struct Block {
    pub name: String,
    pub instructions: Vec<Inst>,
}

impl std::fmt::Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(\n{}\n)",
            indent_lines(join(&self.instructions, "\n"), 2)
        )
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
    pub params: Vec<Local>,
    pub locals: Vec<Local>,
    pub ty: FunctionType,
    pub body: Block,
    pub symbols: SymbolSet,
}

impl std::fmt::Display for Func {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "fn {}({}) {{\n{}\n}}",
            self.name,
            join(&self.params, ", "),
            indent_lines(&self.body, 2)
        )
    }
}

#[derive(Clone, Debug)]
pub struct FuncRef {
    name: String,
    ty: FunctionType,
}

impl std::fmt::Display for FuncRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "$fn[{}]", self.name)
    }
}

#[derive(Clone, Debug)]
pub struct Call {
    fn_name: String,
    original_fn: String,
    fn_ref: Local,
    args: Vec<Atom>,
    ty: FunctionType,
}

LirImplInto!(Value for Call);

impl std::fmt::Display for Call {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", self.fn_name, join(&self.args, ", "))
    }
}

#[derive(Clone, Debug)]
pub struct CExternCall {
    fn_name: String,
    args: Vec<Atom>,
    ty: FunctionType,
}

LirImplInto!(Value for CExternCall);

impl std::fmt::Display for CExternCall {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@extern {}({})", self.fn_name, join(&self.args, ", "))
    }
}

#[derive(Clone, Debug)]
pub struct IfBlock {
    name: String,
    cond: Block,
    then: Block,
    els: Block,
    end: Block,
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

#[derive(Clone, Debug)]
pub struct Loop {
    name: String,
    begin: Block,
    cond: Block,
    body: Block,
    end: Block,
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

#[derive(Clone, Debug)]
pub struct Store {
    dst: Variable,
    value: Value,
    offset: Size,
    size: Size,
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

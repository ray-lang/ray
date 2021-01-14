use crate::{ast, sym};

use std::collections::{HashMap, HashSet};

// stand in for types
#[derive(Debug)]
pub struct FunctionType;
#[derive(Debug)]
pub struct SymbolSet;
#[derive(Debug)]
pub struct TypeMetadata;

#[derive(Debug)]
pub enum Variable {
    Data(usize),
    Global(usize),
    Local(usize),
}

#[derive(Debug)]
pub enum Atom {
    Variable(Variable),
    FuncRef(FuncRef),
    UintConst(u64, Size),
    IntConst(i64, Size),
    FloatConst(f64, Size),
    RawString(String),
    NilConst,
}

#[derive(Debug)]
pub enum Value {
    Atom(Atom),
    Malloc(Size),
    Alloca(Size),
    Call(Call),
    CExternCall(CExternCall),
    Branch(Branch),
    Select(Select),
    Load(Load),
    Lea(Lea),
    BinOp(BinOp),
    IntConvert(IntConvert),
}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct Inst {
    pub kind: InstKind,
    pub comment: String,
}

#[derive(Debug)]
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

#[derive(Debug)]
pub enum BranchOp {
    BranchNZ,
    BranchZ,
}

#[derive(Debug)]
pub struct Size {
    ptrs: i8,
    bytes: i8,
}

#[derive(Debug)]
pub struct Extern {
    name: String,
    ty: FunctionType,
    iscC: bool,
}

#[derive(Debug)]
pub struct PolyFuncRef {
    name: String,              // this is the "simple" func name
    func_ctx: String,          // the name of the enclosing function
    poly_type: FunctionType,   // the polymorphic type
    callee_type: FunctionType, // the type of the callee (which may be polymorphic as well)
}

#[derive(Debug)]
pub struct Program {
    module_path: ast::Path,
    globals: Vec<Global>,
    data: Vec<Data>,
    funcs: Vec<Func>,
    externs: Vec<Extern>,
    defined_symbols: HashSet<sym::Symbol>,
    undefined_symbols: HashSet<sym::Symbol>,
    type_metadata: HashMap<String, TypeMetadata>,
    module_map_idx: i64,    // data index for __module_map
    type_metadata_idx: i64, // data index for __type_metadata
    init_func: String,      // module init func
    main: i64,              // index in Funcs for main
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

#[derive(Debug)]
pub struct Data {
    idx: usize,
    name: String,
    initial_value: Vec<i8>,
    ty: ast::Type,
    size: Size,
}

#[derive(Debug)]
pub struct Global {
    idx: usize,
    name: String,
    ty: ast::Type,
    size: Size,
}

#[derive(Clone, Debug)]
pub struct Local {
    pub idx: usize,
    pub name: String,
    pub ty: ast::Type,
    pub is_alloca: bool,
    // size: Size,
    // signed: bool,
}

impl Local {
    pub fn new(idx: usize, ty: ast::Type) -> Local {
        Local {
            idx,
            ty,
            name: String::new(),
            is_alloca: false,
        }
    }
}

// impl Local {
//     pub fn set_type(&self, ty: typing::ast::Type) {
//         // self.size = getTypeSize(ty);
//         // self.signed = getTypeSign(ty);
//         self.ty = ty
//     }
// }

#[derive(Debug)]
pub struct Block {
    name: String,
    instructions: Vec<Inst>,
}

#[derive(Debug)]
pub struct Func {
    pub name: String,
    pub params: Vec<Local>,
    pub locals: Vec<Local>,
    pub ty: FunctionType,
    pub body: Block,
    pub symbols: SymbolSet,
}

#[derive(Debug)]
pub struct FuncRef {
    name: String,
    ty: FunctionType,
}

#[derive(Debug)]
pub struct Call {
    fn_name: String,
    original_fn: String,
    fn_ref: Local,
    args: Vec<Atom>,
    ty: FunctionType,
}

#[derive(Debug)]
pub struct CExternCall {
    fn_name: String,
    args: Vec<Atom>,
    ty: FunctionType,
}

#[derive(Debug)]
pub struct IfBlock {
    name: String,
    cond: Block,
    then: Block,
    els: Block,
    end: Block,
}

#[derive(Debug)]
pub struct Loop {
    name: String,
    begin: Block,
    cond: Block,
    body: Block,
    end: Block,
}

#[derive(Debug)]
pub struct Branch {
    op: BranchOp,
    operand: Atom,
    then_label: String,
    else_label: String,
}

#[derive(Debug)]
pub struct Select {
    cond: Variable,
    then: Atom,
    els: Atom,
}

#[derive(Debug)]
pub struct Store {
    dst: Variable,
    value: Value,
    col: Size,
    size: Size,
}

#[derive(Debug)]
pub struct Load {
    src: Variable,
    col: Size,
    size: Size,
}

#[derive(Debug)]
pub struct Lea {
    value: Atom,
    src_offset: Size,
    dst_offset: Size,
}

#[derive(Debug)]
pub struct BinOp {
    op: Op,
    size: Size,
    signed: bool,
    operands: Vec<Atom>,
}

#[derive(Debug)]
pub struct IntConvert {
    value: Atom,
    src: (Size, bool),
    dst: (Size, bool),
}

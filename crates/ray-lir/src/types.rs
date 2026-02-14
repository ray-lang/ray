use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::Display,
    iter::Sum,
    usize,
};

use petgraph::{
    graph::NodeIndex,
    visit::{Dfs, DfsEvent, EdgeRef, depth_first_search},
};
use ray_shared::{
    local_binding::LocalBindingId,
    node_id::NodeId,
    pathlib::{ItemPath, ModulePath, Path},
    span::Source,
    str,
    ty::Ty,
    unless,
    utils::{join, map_join},
};
use ray_typing::types::{ImplTy, StructTy, Subst, Substitutable, TyScheme};
use serde::{Deserialize, Serialize};

use ray_core::{ast::Modifier, convert::ToSet, strutils::indent_lines};

use crate::{IntrinsicKind, RAY_MAIN_FUNCTION};

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

    fn count_local_uses(&'a self) -> HashMap<usize, usize> {
        let locals = self.get_locals();
        let mut map = HashMap::new();
        for &loc in locals {
            let count = map.entry(loc).or_default();
            *count += 1;
        }
        map
    }
}

impl<'a, T> GetLocals<'a> for Vec<T>
where
    T: GetLocals<'a> + 'a,
{
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.iter().flat_map(|t| t.get_locals()).collect()
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
    fn replace_local(&'a mut self, old: usize, new: usize);
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

    fn replace_local(&'a mut self, old: usize, new: usize) {
        for local in self.get_locals_mut() {
            if *local == old {
                *local = new;
            }
        }
    }
}

pub trait ReindexLabels {
    fn reindex_labels(self, label_map: &HashMap<usize, usize>);
}

impl<'a, I> ReindexLabels for I
where
    I: IntoIterator<Item = &'a mut Inst>,
{
    fn reindex_labels(self, label_map: &HashMap<usize, usize>) {
        for inst in self.into_iter() {
            match inst {
                Inst::Goto(label) => {
                    if let Some(new_label) = label_map.get(label).copied() {
                        *label = new_label
                    }
                }
                Inst::If(If {
                    then_label,
                    else_label,
                    ..
                }) => {
                    if let Some(new_label) = label_map.get(then_label).copied() {
                        *then_label = new_label
                    }
                    if let Some(new_label) = label_map.get(else_label).copied() {
                        *else_label = new_label
                    }
                }
                Inst::Free(_)
                | Inst::Call(_)
                | Inst::CExternCall(_)
                | Inst::SetGlobal(_, _)
                | Inst::SetLocal(_, _)
                | Inst::Store(_)
                | Inst::Insert(_)
                | Inst::StructInit(_, _)
                | Inst::SetField(_)
                | Inst::MemCopy(_, _, _)
                | Inst::IncRef(_, _)
                | Inst::DecRef(_)
                | Inst::Return(_)
                | Inst::Break(_) => continue,
            }
        }
    }
}

pub type ControlFlowGraph = petgraph::stable_graph::StableDiGraph<usize, (), usize>;

pub trait LCA<N> {
    fn lowest_common_ancestor(&self, a: N, b: N, ignore: &Vec<N>) -> Option<N>;
}

impl LCA<usize> for ControlFlowGraph {
    fn lowest_common_ancestor(&self, a: usize, b: usize, ignore: &Vec<usize>) -> Option<usize> {
        let mut dfs_a = Dfs::new(&self, NodeIndex::new(a));
        while let Some(x) = dfs_a.next(&self) {
            if ignore.contains(&x.index()) {
                continue;
            }

            let mut dfs_b = Dfs::new(&self, NodeIndex::new(b));
            while let Some(y) = dfs_b.next(&self) {
                if ignore.contains(&y.index()) {
                    continue;
                }

                if x == y {
                    return Some(x.index());
                }
            }
        }
        None
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SymbolSet(HashSet<Path>);

impl std::ops::Deref for SymbolSet {
    type Target = HashSet<Path>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for SymbolSet {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl IntoIterator for SymbolSet {
    type Item = Path;

    type IntoIter = std::collections::hash_set::IntoIter<Path>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Substitutable for SymbolSet {
    fn apply_subst(&mut self, subst: &Subst) {
        let paths = self.drain().collect::<Vec<_>>();
        for mut path in paths {
            path.apply_subst(subst);
            self.insert(path);
        }
    }
}

impl SymbolSet {
    pub fn new() -> SymbolSet {
        SymbolSet(HashSet::new())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TypeMetadata;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Variable {
    Data(Path, usize),
    Global(Path, usize),
    Local(usize),
    Unit,
}

LirImplInto!(Atom for Variable);

impl Variable {
    #[inline(always)]
    pub fn is_local(&self) -> bool {
        matches!(self, Variable::Local(_))
    }
}

impl Into<Value> for Variable {
    fn into(self) -> Value {
        Value::new(Atom::Variable(self))
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Variable::Data(path, idx) => write!(f, "{}::$data[{}]", path, idx),
            Variable::Global(path, idx) => write!(f, "{}::$global[{}]", path, idx),
            Variable::Local(s) => write!(f, "${}", s),
            Variable::Unit => write!(f, "unit"),
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

impl Substitutable for Variable {
    fn apply_subst(&mut self, _: &Subst) {
        /* do nothing */
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Atom {
    Variable(Variable),
    FuncRef(FuncRef),
    Size(Size),
    BoolConst(bool),
    CharConst(char),
    UintConst(u64, Size),
    IntConst(i64, Size),
    FloatConst(f64, Size),
    RawString(String),
    NilConst,
}

LirImplInto!(Value for Atom);

impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Atom::Variable(v) => write!(f, "{}", v),
            Atom::FuncRef(r) => write!(f, "{}", r),
            Atom::Size(s) => write!(f, "{}", s),
            Atom::BoolConst(b) => write!(f, "{}", b),
            Atom::CharConst(ch) => write!(f, "`{}`", ch),
            Atom::UintConst(u, ..) => write!(f, "{}", u),
            Atom::IntConst(i, ..) => write!(f, "{}", i),
            Atom::FloatConst(c, ..) => write!(f, "{}", c),
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
            | Atom::BoolConst(_)
            | Atom::CharConst(_)
            | Atom::UintConst(..)
            | Atom::IntConst(..)
            | Atom::FloatConst(..)
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
            | Atom::BoolConst(_)
            | Atom::CharConst(_)
            | Atom::UintConst(..)
            | Atom::IntConst(..)
            | Atom::FloatConst(..)
            | Atom::RawString(_)
            | Atom::NilConst => vec![],
        }
    }
}

impl Substitutable for Atom {
    fn apply_subst(&mut self, subst: &Subst) {
        match self {
            Atom::Variable(v) => v.apply_subst(subst),
            Atom::FuncRef(r) => r.apply_subst(subst),
            _ => {}
        }
    }
}

impl Atom {
    pub fn new<A: Into<Atom>>(a: A) -> Atom {
        a.into()
    }

    pub fn uptr(value: u64) -> Atom {
        Atom::UintConst(value, Size::ptr())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Malloc {
    pub ty: TyScheme,
    pub count: Atom,
}
LirImplInto!(Value for Malloc);

impl Display for Malloc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "new({}, {})", self.ty, self.count)
    }
}

impl<'a> GetLocals<'a> for Malloc {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        vec![]
    }
}

impl<'a> GetLocalsMut<'a> for Malloc {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        vec![]
    }
}

impl Substitutable for Malloc {
    fn apply_subst(&mut self, _: &Subst) {
        /* do nothing */
    }
}

impl Malloc {
    pub fn new(ty: TyScheme, count: Atom) -> Value {
        Malloc { ty, count }.into()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Value {
    Empty,
    VarRef(String),
    Atom(Atom),
    Malloc(Malloc),
    Call(Call),
    CExternCall(CExternCall),
    Select(Select),
    Phi(Phi),
    Load(Load),
    Extract(Extract),
    Lea(Lea),
    GetField(GetField),
    BasicOp(BasicOp),
    Cast(Cast),
    IntConvert(IntConvert),
    Type(TyScheme),
    Closure(Closure),
}

impl Value {
    pub fn local(&self) -> Option<usize> {
        if let &Value::Atom(Atom::Variable(Variable::Local(idx))) = self {
            Some(idx)
        } else {
            None
        }
    }

    pub fn var(&self) -> Option<&Variable> {
        if let Value::Atom(Atom::Variable(v)) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Empty => write!(f, ""),
            Value::VarRef(n) => write!(f, "${}", n),
            Value::Atom(a) => write!(f, "{}", a),
            Value::Malloc(a) => write!(f, "{}", a),
            Value::Call(a) => write!(f, "{}", a),
            Value::CExternCall(a) => write!(f, "{}", a),
            Value::Select(a) => write!(f, "{}", a),
            Value::Phi(a) => write!(f, "{}", a),
            Value::Load(a) => write!(f, "{}", a),
            Value::Extract(a) => write!(f, "{}", a),
            Value::Lea(a) => write!(f, "{}", a),
            Value::GetField(a) => write!(f, "{}", a),
            Value::BasicOp(a) => write!(f, "{}", a),
            Value::Cast(c) => write!(f, "{}", c),
            Value::IntConvert(a) => write!(f, "{}", a),
            Value::Type(ty) => write!(f, "type({})", ty),
            Value::Closure(c) => write!(f, "closure({}, {})", c.fn_name, c.env),
        }
    }
}

impl Default for Value {
    fn default() -> Self {
        Value::Empty
    }
}

impl<'a> GetLocalsMut<'a> for Value {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        match self {
            Value::Atom(a) => a.get_locals_mut(),
            Value::Call(c) => c.get_locals_mut(),
            Value::CExternCall(c) => c.get_locals_mut(),
            Value::Select(s) => s.get_locals_mut(),
            Value::Phi(p) => p.get_locals_mut(),
            Value::Load(l) => l.get_locals_mut(),
            Value::Extract(e) => e.get_locals_mut(),
            Value::Malloc(m) => m.get_locals_mut(),
            Value::Lea(l) => l.get_locals_mut(),
            Value::GetField(g) => g.get_locals_mut(),
            Value::BasicOp(b) => b.get_locals_mut(),
            Value::Cast(c) => c.get_locals_mut(),
            Value::IntConvert(_) => todo!(),
            Value::Closure(c) => c.get_locals_mut(),
            Value::Type(_) | Value::VarRef(_) | Value::Empty => vec![],
        }
    }
}

impl<'a> GetLocals<'a> for Value {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        match self {
            Value::Atom(a) => a.get_locals(),
            Value::Call(c) => c.get_locals(),
            Value::CExternCall(c) => c.get_locals(),
            Value::Select(s) => s.get_locals(),
            Value::Phi(p) => p.get_locals(),
            Value::Load(l) => l.get_locals(),
            Value::Extract(e) => e.get_locals(),
            Value::Malloc(m) => m.get_locals(),
            Value::Lea(l) => l.get_locals(),
            Value::GetField(g) => g.get_locals(),
            Value::BasicOp(b) => b.get_locals(),
            Value::Cast(c) => c.get_locals(),
            Value::IntConvert(_) => todo!(),
            Value::Closure(c) => c.get_locals(),
            Value::Type(_) | Value::VarRef(_) | Value::Empty => vec![],
        }
    }
}

impl Substitutable for Value {
    fn apply_subst(&mut self, subst: &Subst) {
        match self {
            Value::Empty | Value::VarRef(_) => {}
            Value::Atom(a) => a.apply_subst(subst),
            Value::Malloc(m) => m.apply_subst(subst),
            Value::Call(c) => c.apply_subst(subst),
            Value::CExternCall(_) => todo!(),
            Value::Select(s) => s.apply_subst(subst),
            Value::Phi(phi) => phi.apply_subst(subst),
            Value::Load(l) => l.apply_subst(subst),
            Value::Extract(e) => e.apply_subst(subst),
            Value::Lea(l) => l.apply_subst(subst),
            Value::GetField(g) => g.apply_subst(subst),
            Value::BasicOp(b) => b.apply_subst(subst),
            Value::Cast(c) => c.apply_subst(subst),
            Value::IntConvert(i) => i.apply_subst(subst),
            Value::Type(ty) => ty.apply_subst(subst),
            Value::Closure(c) => c.apply_subst(subst),
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

    pub fn to_inst(self) -> Option<Inst> {
        match self {
            Value::Call(c) => Some(Inst::Call(c)),
            Value::CExternCall(c) => Some(Inst::CExternCall(c)),
            Value::Empty
            | Value::VarRef(_)
            | Value::Atom(_)
            | Value::Malloc(_)
            | Value::Select(_)
            | Value::Phi(_)
            | Value::Load(_)
            | Value::Extract(_)
            | Value::Lea(_)
            | Value::GetField(_)
            | Value::BasicOp(_)
            | Value::Cast(_)
            | Value::Type(_)
            | Value::IntConvert(_)
            | Value::Closure(_) => None,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Inst {
    Free(usize),
    Call(Call),
    CExternCall(CExternCall),
    SetGlobal(usize, Value),
    SetLocal(usize, Value),
    If(If),
    Store(Store),
    Insert(Insert),
    StructInit(Variable, StructTy),
    SetField(SetField),
    MemCopy(Variable, Variable, Atom),
    IncRef(Value, i8),
    DecRef(Value),
    Return(Value),
    Break(Break),
    Goto(usize),
}

impl<'a> Display for FuncDisplayCtx<'a, &Inst> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            Inst::SetLocal(idx, value) => {
                let local = &self.locals[*idx];
                write!(f, "${}: {} = {}", idx, local.ty, value)
            }
            value => write!(f, "{}", value),
        }
    }
}

impl Display for Inst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Inst::Free(s) => write!(f, "free ${}", s),
            Inst::Call(c) => write!(f, "{}", c),
            Inst::CExternCall(_) => todo!(),
            Inst::SetGlobal(s, v) => write!(f, "$global[{}] = {}", s, v),
            Inst::SetLocal(s, v) => write!(f, "${} = {}", s, v),
            Inst::If(b) => write!(f, "{}", b),
            Inst::Store(s) => write!(f, "{}", s),
            Inst::Insert(i) => write!(f, "{}", i),
            Inst::StructInit(v, ty) => write!(f, "{}: {}", v, ty),
            Inst::SetField(s) => write!(f, "{}", s),
            Inst::IncRef(v, i) => write!(f, "incref {} {}", v, i),
            Inst::DecRef(v) => write!(f, "decref {}", v),
            Inst::Return(v) => write!(f, "ret {}", v),
            Inst::Goto(idx) => write!(f, "goto B{}", idx),
            Inst::MemCopy(dst, src, size) => {
                write!(f, "memcpy dst={} src={} size={}", dst, src, size)
            }
            Inst::Break(b) => write!(f, "{}", b),
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
            Inst::If(b) => b.get_locals_mut(),
            Inst::Store(s) => s.get_locals_mut(),
            Inst::Insert(i) => i.get_locals_mut(),
            Inst::StructInit(v, _) => v.get_locals_mut(),
            Inst::SetField(s) => s.get_locals_mut(),
            Inst::MemCopy(d, s, z) => {
                let mut locs = d.get_locals_mut();
                locs.extend(s.get_locals_mut());
                locs.extend(z.get_locals_mut());
                locs
            }
            Inst::Call(c) => c.get_locals_mut(),
            Inst::CExternCall(c) => c.get_locals_mut(),
            Inst::IncRef(v, _) | Inst::DecRef(v) | Inst::Return(v) => v.get_locals_mut(),
            Inst::Break(b) => b.get_locals_mut(),
            Inst::Goto(_) => vec![],
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
            Inst::If(b) => b.get_locals(),
            Inst::StructInit(v, _) => v.get_locals(),
            Inst::SetField(s) => s.get_locals(),
            Inst::Store(s) => s.get_locals(),
            Inst::Insert(i) => i.get_locals(),
            Inst::MemCopy(d, s, z) => {
                let mut locs = d.get_locals();
                locs.extend(s.get_locals());
                locs.extend(z.get_locals());
                locs
            }
            Inst::Call(c) => c.get_locals(),
            Inst::CExternCall(c) => c.get_locals(),
            Inst::IncRef(v, _) | Inst::DecRef(v) | Inst::Return(v) => v.get_locals(),
            Inst::Break(b) => b.get_locals(),
            Inst::Goto(_) => vec![],
        }
    }
}

impl Substitutable for Inst {
    fn apply_subst(&mut self, subst: &Subst) {
        match self {
            Inst::Call(c) => c.apply_subst(subst),
            Inst::CExternCall(_) => todo!(),
            Inst::SetGlobal(_, v) => v.apply_subst(subst),
            Inst::SetLocal(_, v) => v.apply_subst(subst),
            Inst::If(b) => b.apply_subst(subst),
            Inst::StructInit(v, struct_ty) => {
                v.apply_subst(subst);
                struct_ty.apply_subst(subst);
            }
            Inst::SetField(s) => s.apply_subst(subst),
            Inst::Store(s) => s.apply_subst(subst),
            Inst::Insert(i) => i.apply_subst(subst),
            Inst::MemCopy(d, s, z) => {
                d.apply_subst(subst);
                s.apply_subst(subst);
                z.apply_subst(subst);
            }
            Inst::IncRef(v, _) => v.apply_subst(subst),
            Inst::DecRef(v) => v.apply_subst(subst),
            Inst::Return(v) => v.apply_subst(subst),
            Inst::Break(b) => b.apply_subst(subst),
            Inst::Free(_) | Inst::Goto(_) => {}
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

    pub fn is_control(&self) -> bool {
        matches!(
            self,
            Inst::Break(_) | Inst::Goto(_) | Inst::If(_) | Inst::Return(_)
        )
    }

    pub fn is_jump(&self) -> bool {
        matches!(self, Inst::Goto(_) | Inst::If(_) | Inst::Return(_))
            || matches!(
                self,
                Inst::Break(b) if b.operand.is_none()
            )
    }
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Neg,
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
    And,
    Or,
    Not,
}

impl Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Op::Add => write!(f, "add"),
            Op::Sub => write!(f, "sub"),
            Op::Mul => write!(f, "mul"),
            Op::Div => write!(f, "div"),
            Op::Mod => write!(f, "mod"),
            Op::Neg => write!(f, "neg"),
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
            Op::And => write!(f, "and"),
            Op::Or => write!(f, "or"),
            Op::Not => write!(f, "not"),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum BreakOp {
    Break,
    BreakNZ,
    BreakZ,
}

impl Display for BreakOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BreakOp::Break => write!(f, "break"),
            BreakOp::BreakNZ => write!(f, "breaknz"),
            BreakOp::BreakZ => write!(f, "breakz"),
        }
    }
}

pub trait SizeOf {
    fn size_of(&self) -> Size;
}

impl SizeOf for Ty {
    fn size_of(&self) -> Size {
        match self {
            Ty::Never | Ty::Any | Ty::Var(_) => Size::zero(),
            Ty::Array(t, size) => t.size_of() * *size,
            Ty::Tuple(t) => t.iter().map(Ty::size_of).sum(),
            Ty::Func(_, _) | Ty::Ref(_) | Ty::RawPtr(_) => Size::ptr(),
            Ty::Proj(ty, params) => {
                // Special-case `nilable['a]` to have an explicit Option-like
                // layout: a 1-byte discriminant plus the payload `'a`.
                if ty.as_str() == "nilable" {
                    let payload_size = params
                        .get(0)
                        .map(|t| t.size_of())
                        .unwrap_or_else(Size::zero);
                    return Size::bytes(1) + payload_size;
                }

                // For all other projections, fall back to the underlying type's
                // size (this matches the previous behavior).
                Size::ptr()
            }
            Ty::Const(n) => match n.as_str() {
                "int" | "uint" => Size::ptr(),
                "i8" | "u8" | "bool" => Size::bytes(1),
                "i16" | "u16" => Size::bytes(2),
                "i32" | "u32" | "f32" => Size::bytes(4),
                "i64" | "u64" | "f64" => Size::bytes(8),
                "i128" | "u128" | "f128" => Size::bytes(16),
                _ => Size::ptr(),
            },
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
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

impl Display for Size {
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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Extern {
    pub name: Path,
    pub ty: TyScheme,
    pub is_mutable: bool,
    pub modifiers: Vec<Modifier>,
    pub is_intrinsic: bool,
    pub intrinsic_kind: Option<IntrinsicKind>,
    pub src: Option<String>,
}

impl Display for Extern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "extern {} : {}", self.name, self.ty)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Program {
    pub module_path: ModulePath,
    pub globals: Vec<Global>,
    pub data: Vec<Data>,
    pub funcs: Vec<Func>,
    pub externs: Vec<Extern>,
    pub extern_map: HashMap<Path, usize>,
    pub trait_member_set: HashSet<Path>,
    pub poly_fn_map: HashMap<Path, Vec<usize>>,
    /// Side table of available impls keyed by trait FQN.
    ///
    /// This is populated from the typing context and extended across linked
    /// libraries. The monomorphizer uses it to validate impl-qualifiers when
    /// selecting between overlapping polymorphic impl bodies.
    pub impls_by_trait: BTreeMap<ItemPath, Vec<ImplTy>>,
    pub start_idx: i64,       // index in Funcs for _start
    pub module_main_idx: i64, // index in Funcs for module main
    pub user_main_idx: i64,   // index in Funcs for user main
    pub resolved_user_main: Option<Path>,
    /// All struct types needed for codegen.
    ///
    /// Includes both workspace struct definitions and synthetic structs
    /// (closure environment types, function handle types, etc.).
    pub struct_types: HashMap<ItemPath, StructTy>,
}

impl Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &join(&self.externs, "\n"))?;

        if !self.externs.is_empty() {
            write!(f, "\n\n")?;
        }

        write!(f, "{}", &join(&self.funcs, "\n\n"))
    }
}

impl Substitutable for Program {
    fn apply_subst(&mut self, subst: &Subst) {
        for global in &mut self.globals {
            global.ty.apply_subst(subst);
        }

        for func in &mut self.funcs {
            func.apply_subst(subst);
        }

        for ext in &mut self.externs {
            ext.ty.apply_subst(subst);
        }

        for bucket in self.impls_by_trait.values_mut() {
            for impl_ty in bucket {
                impl_ty.apply_subst(subst);
            }
        }
    }
}

impl Program {
    pub fn new(m: impl Into<ModulePath>) -> Program {
        let m = m.into();
        Program {
            module_path: m,
            globals: vec![],
            data: vec![],
            funcs: vec![],
            externs: vec![],
            poly_fn_map: HashMap::new(),
            extern_map: HashMap::new(),
            trait_member_set: HashSet::new(),
            impls_by_trait: BTreeMap::new(),
            start_idx: -1,
            module_main_idx: -1,
            user_main_idx: -1,
            resolved_user_main: None,
            struct_types: HashMap::new(),
        }
    }

    pub fn extend(&mut self, other: Program) {
        let func_offset = self.funcs.len();
        for (p, indices) in other.poly_fn_map {
            let offset_indices: Vec<usize> = indices.into_iter().map(|i| func_offset + i).collect();
            self.poly_fn_map
                .entry(p)
                .or_default()
                .extend(offset_indices);
        }

        self.globals.extend(other.globals);
        self.data.extend(other.data);
        self.funcs.extend(other.funcs);

        // Offset extern indices before extending
        let extern_offset = self.externs.len();
        self.externs.extend(other.externs);
        for (path, idx) in other.extern_map {
            self.extern_map.insert(path, extern_offset + idx);
        }

        self.trait_member_set.extend(other.trait_member_set);
        self.struct_types.extend(other.struct_types);
        for (trait_name, bucket) in other.impls_by_trait {
            self.impls_by_trait
                .entry(trait_name)
                .or_default()
                .extend(bucket);
        }
    }

    pub fn module_main_path(&self) -> Path {
        self.module_path
            .to_path()
            .append(RAY_MAIN_FUNCTION)
            .append_func_type(vec![Ty::unit()], Ty::unit())
    }

    pub fn user_main_path(&self) -> Path {
        self.resolved_user_main
            .clone()
            .unwrap_or_else(|| self.module_path.to_path().append("main"))
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Data {
    idx: usize,
    path: Path,
    value: Vec<u8>,
}

impl Data {
    pub fn new(idx: usize, path: Path, value: Vec<u8>) -> Data {
        Data { idx, path, value }
    }

    pub fn key(&self) -> (Path, usize) {
        (self.path.clone(), self.idx)
    }

    pub fn index(&self) -> usize {
        self.idx
    }

    pub fn name(&self) -> String {
        format!("{}::/data::{}", self.path, self.idx)
    }

    pub fn value(&self) -> Vec<u8> {
        self.value.clone()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Global {
    pub idx: usize,
    pub path: Path,
    pub name: String,
    pub ty: TyScheme,
    pub init_value: Value,
    pub mutable: bool,
}

impl Substitutable for Global {
    fn apply_subst(&mut self, subst: &Subst) {
        self.ty.apply_subst(subst);
        self.init_value.apply_subst(subst);
    }
}

impl Global {
    pub fn key(&self) -> (Path, usize) {
        (self.path.clone(), self.idx)
    }

    pub fn name(&self) -> String {
        format!("{}::/global::{}", self.path, self.name)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Local {
    pub idx: usize,
    pub ty: TyScheme,
}

impl Display for Local {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.idx)
    }
}

impl Substitutable for Local {
    fn apply_subst(&mut self, subst: &Subst) {
        self.ty.apply_subst(subst);
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
    pub fn new(idx: usize, ty: TyScheme) -> Local {
        Local { idx, ty }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Param {
    pub name: String,
    pub idx: usize,
    pub ty: Ty,
}

impl Display for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}: {}", self.idx, self.ty)
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

impl Substitutable for Param {
    fn apply_subst(&mut self, subst: &Subst) {
        self.ty.apply_subst(subst);
    }
}

impl Param {
    pub fn new(name: String, idx: usize, ty: Ty) -> Param {
        Param { name, idx, ty }
    }
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum ControlMarker {
    If,
    Else(usize),
    Loop,
    End(usize),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Block {
    label: usize,
    instructions: Vec<Inst>,
    defined_vars: HashMap<String, usize>,
    markers: Vec<ControlMarker>,
}

impl<'a> Display for FuncDisplayCtx<'a, &Block> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let lines = indent_lines(
            map_join(&self.value.instructions, "\n", |inst| {
                format!("{}", self.with(inst))
            }),
            2,
        );
        let mut markers = map_join(&self.value.markers, ", ", |marker| match marker {
            ControlMarker::If => str!("#if"),
            ControlMarker::Else(label) => format!("#else({})", label),
            ControlMarker::Loop => str!("#loop"),
            ControlMarker::End(label) => format!("#end({})", label),
        });
        if markers.len() != 0 {
            markers.insert_str(0, "  ");
        }
        write!(f, "B{}:{}\n{}", self.value.label, markers, lines)
    }
}

impl std::ops::Deref for Block {
    type Target = Vec<Inst>;

    fn deref(&self) -> &Self::Target {
        &self.instructions
    }
}

impl std::ops::DerefMut for Block {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.instructions
    }
}

impl Extend<Inst> for Block {
    fn extend<T: IntoIterator<Item = Inst>>(&mut self, iter: T) {
        self.instructions.extend(iter);
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

impl Substitutable for Block {
    fn apply_subst(&mut self, subst: &Subst) {
        self.instructions.apply_subst(subst)
    }
}

impl Block {
    pub fn new(label: usize) -> Block {
        Block {
            label,
            instructions: vec![],
            defined_vars: HashMap::new(),
            markers: vec![],
        }
    }

    #[inline(always)]
    pub fn label(&self) -> usize {
        self.label
    }

    #[inline(always)]
    pub fn label_mut(&mut self) -> &mut usize {
        &mut self.label
    }

    #[inline(always)]
    pub fn markers(&self) -> &Vec<ControlMarker> {
        &self.markers
    }

    #[inline(always)]
    pub fn markers_mut(&mut self) -> &mut Vec<ControlMarker> {
        &mut self.markers
    }

    #[inline(always)]
    pub fn is_loop_header(&self) -> bool {
        self.markers
            .iter()
            .any(|&marker| matches!(marker, ControlMarker::Loop))
    }

    #[inline(always)]
    pub fn is_if_header(&self) -> bool {
        self.markers
            .iter()
            .any(|&marker| matches!(marker, ControlMarker::If))
    }

    #[inline(always)]
    pub fn is_else(&self, label: usize) -> bool {
        self.markers
            .iter()
            .any(|&marker| matches!(marker, ControlMarker::Else(l) if l == label))
    }

    #[inline(always)]
    pub fn is_end(&self, label: usize) -> bool {
        self.markers
            .iter()
            .any(|&marker| matches!(marker, ControlMarker::End(l) if l == label))
    }

    #[inline(always)]
    pub fn defined_vars(&self) -> &HashMap<String, usize> {
        &self.defined_vars
    }

    #[inline(always)]
    pub fn define_var(&mut self, var: String, idx: usize) {
        log::debug!("define var: {} -> {}", var, idx);
        self.defined_vars.insert(var, idx);
    }

    pub fn phi(&mut self, idx: usize, value: (usize, usize)) {
        let mut inst_idx = 0;
        while inst_idx < self.len() {
            match &mut self[inst_idx] {
                Inst::SetLocal(loc, Value::Phi(Phi(values))) if loc == &idx => {
                    // the value here unless it already exists
                    if !values.contains(&value) {
                        values.push(value);
                    }
                    return;
                }
                Inst::SetLocal(_, Value::Phi(_)) => inst_idx += 1,
                _ => break,
            }
        }
        self.insert(inst_idx, Inst::SetLocal(idx, Phi::new(vec![value]).into()));
    }

    pub fn split_off(&mut self, idx: usize) -> Block {
        let instructions = self.instructions.split_off(idx + 1);

        // create a map of indices to names
        let mut reverse_map = HashMap::new();
        let mut defined_vars = self.defined_vars.drain().collect::<HashMap<_, _>>();
        for (k, v) in defined_vars.iter() {
            reverse_map.insert(*v, k.clone());
        }

        // find all of the defined variables
        for inst in self.instructions.iter() {
            if let Inst::SetLocal(idx, _) = inst {
                if let Some(name) = reverse_map.remove(idx) {
                    defined_vars.remove(&name);
                    self.defined_vars.insert(name, *idx);
                }
            }
        }

        // create the new block with an undefined label
        Block {
            label: usize::MAX,
            instructions,
            defined_vars,
            markers: self.markers.clone(),
        }
    }
}

pub type DominatorFrontiers = HashMap<usize, HashSet<usize>>;

#[derive(Debug)]
pub struct Loop {
    pub back_edge: (usize, usize),
    pub nodes: Vec<usize>,
    pub exit_edges: Vec<(usize, usize)>,
    pub common_exit: usize,
}

impl Loop {
    #[inline(always)]
    pub fn header(&self) -> usize {
        self.back_edge.1
    }

    pub fn is_exit_node(&self, n: usize) -> bool {
        self.exit_edges.iter().any(|(_, a)| a == &n)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Func {
    pub name: Path,
    pub params: Vec<Param>,
    pub locals: Vec<Local>,
    pub ty: TyScheme,
    pub blocks: Vec<Block>,
    pub symbols: SymbolSet,
    pub modifiers: Vec<Modifier>,
    pub cfg: ControlFlowGraph,
    /// The source AST node this function was generated from, if any.
    /// `None` for synthetic functions like `_start` and module main.
    pub source_id: Option<NodeId>,
}

pub struct FuncDisplayCtx<'a, T> {
    value: T,
    locals: &'a Vec<Local>,
}

impl<'a, T> FuncDisplayCtx<'a, T> {
    pub fn new(value: T, locals: &'a Vec<Local>) -> Self {
        Self { value, locals }
    }

    pub fn with<U>(&self, value: U) -> FuncDisplayCtx<'a, U> {
        FuncDisplayCtx {
            value,
            locals: self.locals,
        }
    }
}

impl Display for Func {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (_, preds, _, ret_ty) = self.ty.try_borrow_fn().unwrap();
        write!(
            f,
            "fn {}({}) -> {}{} {{\n{}\n}}",
            self.name,
            map_join(&self.params, ", ", |p| format!("${}: {}", p.idx, p.ty)),
            ret_ty,
            if !preds.is_empty() {
                format!(" where {}", join(preds, " + "))
            } else {
                str!("")
            },
            indent_lines(
                map_join(&self.blocks, "\n", |block| {
                    format!("{}", FuncDisplayCtx::new(block, &self.locals))
                }),
                2,
            )
        )
    }
}

impl<'a> GetLocalsMut<'a> for Func {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        let mut locs = self.locals.get_locals_mut();
        locs.extend(self.params.get_locals_mut());
        locs.extend(self.blocks.get_locals_mut());
        locs
    }
}

impl<'a> GetLocals<'a> for Func {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        let mut locs = self.locals.get_locals();
        locs.extend(self.params.get_locals());
        locs.extend(self.blocks.get_locals());
        locs
    }
}

impl Substitutable for Func {
    fn apply_subst(&mut self, subst: &Subst) {
        self.name.apply_subst(subst);
        self.ty.apply_subst(subst);
        self.params.apply_subst(subst);
        self.locals.apply_subst(subst);
        self.blocks.apply_subst(subst);
        self.symbols.apply_subst(subst);
    }
}

impl Func {
    pub fn new(
        name: Path,
        ty: TyScheme,
        modifiers: Vec<Modifier>,
        symbols: SymbolSet,
        cfg: ControlFlowGraph,
        source_id: Option<NodeId>,
    ) -> Func {
        Func {
            name,
            ty,
            modifiers,
            symbols,
            cfg,
            source_id,
            params: vec![],
            locals: vec![],
            blocks: vec![],
        }
    }

    pub fn ty_of_local(&self, loc: usize) -> Option<TyScheme> {
        self.locals.iter().find_map(|l| {
            if l.idx == loc {
                Some(l.ty.clone())
            } else {
                None
            }
        })
    }

    pub fn set_ty_of_local(&mut self, loc: usize, ty: TyScheme) {
        if let Some(l) = self.locals.iter_mut().find(|l| l.idx == loc) {
            l.ty = ty;
        }
    }

    pub fn reindex_blocks(&mut self) {
        let mut label_map = HashMap::new();
        for new_label in 0..self.blocks.len() {
            let block = &mut self.blocks[new_label];
            let label = block.label_mut();
            let prev_label = *label;
            if new_label == prev_label {
                continue;
            }

            *label = new_label;
            label_map.insert(prev_label, new_label);
        }

        for block in self.blocks.iter_mut() {
            block.reindex_labels(&label_map);
        }
    }

    pub fn inline(
        mut self,
        args: Vec<Variable>,
        _: Option<Variable>,
        local_offset: usize,
    ) -> (Vec<Local>, Vec<Block>) {
        self.offset_locals(local_offset);

        let mut params_block = Block::new(usize::MAX);
        params_block.instructions.extend(
            self.params
                .iter()
                .zip(args.into_iter())
                .map(|(p, a)| Inst::SetLocal(p.idx, Atom::new(a).into())),
        );

        // TODO: we need to somehow to find all of the returns and then
        // set the result local to a phi node based on the returns...?
        todo!()
    }

    pub fn find_loops(&self) -> HashMap<usize, Loop> {
        // using the CFG, find the loops
        let mut loops = HashMap::new();
        let sccs = petgraph::algo::tarjan_scc(&self.cfg);

        // first, find all of the back edges
        let mut back_edges = vec![];
        if self.cfg.edge_count() != 0 {
            depth_first_search(&self.cfg, Some(NodeIndex::new(0)), |event| {
                if let DfsEvent::BackEdge(b, h) = event {
                    back_edges.push((b.index(), h.index()));
                }
            });
        }

        // the order of the sccs is their postorder, so iterate in reverse
        for nodes in sccs.into_iter().rev() {
            // SCCs with more than one node are loops
            if nodes.len() <= 1 {
                continue;
            }

            // create set from the nodes
            let node_set = nodes.iter().map(|n| n.index()).to_set();

            // find the back edge of the loop
            let back_edge = match back_edges
                .iter()
                .find(|(b, h)| node_set.contains(b) && node_set.contains(h))
            {
                Some(&edge) => edge,
                _ => panic!("COMPILER BUG: this loop does not have a back edge"),
            };

            // determine which nodes are exit nodes
            let exit_edges = nodes
                .iter()
                .flat_map(|&n| {
                    // if the node N has a successor that is not contained in the loop
                    self.cfg.edges(n).filter_map(|edge| {
                        let n = edge.source().index();
                        let m = edge.target().index();
                        if !node_set.contains(&m) {
                            Some((n, m))
                        } else {
                            None
                        }
                    })
                })
                .collect::<Vec<(usize, usize)>>();

            // get the path from the header to the back
            let (back, header) = back_edge;
            let (_, nodes) = petgraph::algo::astar(
                &self.cfg,
                NodeIndex::new(header),
                |n| n.index() == back,
                |_| 1,
                |_| 0,
            )
            .unwrap();

            // find the common exit node
            let nodes = nodes.into_iter().map(NodeIndex::index).collect();
            let &(mut common_exit, _) = exit_edges.first().unwrap();
            for &(node, _) in exit_edges.iter().skip(1) {
                common_exit = self
                    .cfg
                    .lowest_common_ancestor(common_exit, node, &nodes)
                    .unwrap();
            }

            loops.insert(
                header,
                Loop {
                    back_edge,
                    nodes,
                    exit_edges,
                    common_exit,
                },
            );
        }

        log::debug!("loops: {:?}", loops);
        loops
    }

    pub fn calculate_dom_frontiers(&self) -> DominatorFrontiers {
        let mut frontiers = DominatorFrontiers::new();
        if self.cfg.edge_count() == 0 {
            // there are no dominators for a graph with no edges
            return frontiers;
        }

        let entry = unless!(self.blocks.get(0), else return frontiers);
        let doms = petgraph::algo::dominators::simple_fast(&self.cfg, entry.label().into());

        for block in self.blocks.iter() {
            let index = block.label().into();
            let preds = self
                .cfg
                .neighbors_directed(index, petgraph::EdgeDirection::Incoming)
                .collect::<Vec<_>>();
            if preds.len() <= 1 {
                continue;
            }

            for pred in preds {
                let mut runner = pred;
                while Some(runner) != doms.immediate_dominator(index) {
                    frontiers
                        .entry(runner.index())
                        .or_default()
                        .insert(block.label());
                    runner = unless!(doms.immediate_dominator(runner), else break);
                }
            }
        }

        frontiers
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FuncRef {
    pub path: Path,
    pub original_path: Path,
    pub ty: TyScheme,
    pub poly_ty: Option<TyScheme>,
}

impl FuncRef {
    pub fn new(path: Path, ty: TyScheme) -> Self {
        let original_path = path.with_names_only();
        Self {
            path,
            original_path,
            ty,
            poly_ty: None,
        }
    }
}

impl Display for FuncRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "$fn[{}]", self.path)
    }
}

impl Substitutable for FuncRef {
    fn apply_subst(&mut self, subst: &Subst) {
        self.ty.apply_subst(subst);
        if let Some(poly) = &mut self.poly_ty {
            poly.apply_subst(subst);
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Call {
    pub fn_name: Path,
    pub original_fn_name: Path,
    pub fn_ref: Option<usize>,
    pub args: Vec<Variable>,
    pub callee_ty: TyScheme,
    pub poly_callee_ty: Option<TyScheme>,
    pub source: Option<Source>,
}

LirImplInto!(Inst for Call);
LirImplInto!(Value for Call);

impl Display for Call {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(fn_ref) = self.fn_ref {
            write!(f, "${}", fn_ref)?;
        } else {
            write!(f, "{}", self.fn_name)?;
        }
        write!(f, "({})", join(&self.args, ", "))
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

impl Substitutable for Call {
    fn apply_subst(&mut self, subst: &Subst) {
        self.fn_name.apply_subst(subst);
        self.args.apply_subst(subst);
        self.callee_ty.apply_subst(subst);
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
    pub fn new(
        fn_name: Path,
        args: Vec<Variable>,
        ty: TyScheme,
        poly_ty: Option<TyScheme>,
    ) -> Call {
        Call {
            original_fn_name: fn_name.clone(),
            fn_ref: None,
            callee_ty: ty,
            poly_callee_ty: poly_ty,
            args,
            fn_name,
            source: None,
        }
    }

    pub fn new_ref(
        fn_ref: usize,
        args: Vec<Variable>,
        ty: TyScheme,
        poly_ty: Option<TyScheme>,
    ) -> Call {
        Call {
            original_fn_name: Path::new(),
            fn_name: Path::new(),
            fn_ref: Some(fn_ref),
            callee_ty: ty,
            poly_callee_ty: poly_ty,
            args,
            source: None,
        }
    }

    pub fn orig_name(&self) -> &Path {
        &self.original_fn_name
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CExternCall {
    fn_name: String,
    args: Vec<Atom>,
    ty: Ty,
}

LirImplInto!(Value for CExternCall);

impl Display for CExternCall {
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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct If {
    pub cond_loc: usize,
    pub then_label: usize,
    pub else_label: usize,
}

LirImplInto!(Inst for If);

impl Display for If {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "if ${} then B{} else B{}",
            self.cond_loc, self.then_label, self.else_label,
        )
    }
}

impl<'a> GetLocalsMut<'a> for If {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        vec![&mut self.cond_loc]
    }
}

impl<'a> GetLocals<'a> for If {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        vec![&self.cond_loc]
    }
}

impl Substitutable for If {
    fn apply_subst(&mut self, _: &Subst) {
        /* do nothing */
    }
}

impl If {
    pub fn new(cond_loc: usize, then_label: usize, else_label: usize) -> Self {
        Self {
            cond_loc,
            then_label,
            else_label,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Break {
    pub op: BreakOp,
    pub operand: Option<Atom>,
    pub label: Option<usize>,
}

LirImplInto!(Inst for Break);

impl Display for Break {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let label = self
            .label
            .as_ref()
            .map(|l| format!(" B{}", l))
            .unwrap_or_default();
        let operand = self
            .operand
            .as_ref()
            .map(|a| format!(" {}", a))
            .unwrap_or_default();

        write!(f, "{}{}{}", self.op, operand, label)
    }
}

impl<'a> GetLocalsMut<'a> for Break {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.operand
            .as_mut()
            .map(|o| o.get_locals_mut())
            .unwrap_or_default()
    }
}

impl<'a> GetLocals<'a> for Break {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.operand
            .as_ref()
            .map(|o| o.get_locals())
            .unwrap_or_default()
    }
}

impl Substitutable for Break {
    fn apply_subst(&mut self, subst: &Subst) {
        self.operand.apply_subst(subst);
    }
}

impl Break {
    pub fn new() -> Self {
        Self {
            op: BreakOp::Break,
            operand: None,
            label: None,
        }
    }

    pub fn zero(operand: Atom, label: usize) -> Self {
        Self {
            op: BreakOp::BreakZ,
            operand: Some(operand),
            label: Some(label),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Phi(Vec<(usize, usize)>);

LirImplInto!(Value for Phi);

impl Display for Phi {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "phi({})",
            map_join(self.values(), ", ", |(x, y)| format!("B{}: ${}", x, y))
        )
    }
}

impl<'a> GetLocalsMut<'a> for Phi {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.values_mut().iter_mut().map(|(_, l)| l).collect()
    }
}

impl<'a> GetLocals<'a> for Phi {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.values().iter().map(|(_, l)| l).collect()
    }
}

impl Substitutable for Phi {
    fn apply_subst(&mut self, _: &Subst) {
        /* do nothing */
    }
}

impl Phi {
    pub fn new(values: Vec<(usize, usize)>) -> Self {
        Self(values)
    }

    #[inline(always)]
    pub fn values(&self) -> &Vec<(usize, usize)> {
        &self.0
    }

    #[inline(always)]
    pub fn values_mut(&mut self) -> &mut Vec<(usize, usize)> {
        &mut self.0
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Select {
    pub cond: Variable,
    pub then: Variable,
    pub els: Variable,
}

LirImplInto!(Value for Select);

impl Display for Select {
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

impl Substitutable for Select {
    fn apply_subst(&mut self, subst: &Subst) {
        self.cond.apply_subst(subst);
        self.then.apply_subst(subst);
        self.els.apply_subst(subst);
    }
}

impl Select {
    pub fn new(cond: Variable, then: Variable, els: Variable) -> Self {
        Self { cond, then, els }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Store {
    pub dst: Variable,
    pub value: Value,
    pub offset: usize,
}

impl Display for Store {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "store {} {} offset=({})",
            self.dst, self.value, self.offset,
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

impl Substitutable for Store {
    fn apply_subst(&mut self, subst: &Subst) {
        self.dst.apply_subst(subst);
        self.value.apply_subst(subst);
    }
}

impl Store {
    pub fn new(dst: Variable, value: Value, offset: usize) -> Inst {
        Inst::Store(Store { dst, value, offset })
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Load {
    pub src: Variable,
    pub offset: Size,
}

LirImplInto!(Value for Load);

impl Display for Load {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "load {} offset=({})", self.src, self.offset,)
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

impl Substitutable for Load {
    fn apply_subst(&mut self, subst: &Subst) {
        self.src.apply_subst(subst);
    }
}

impl Load {
    pub fn new(src: Variable, offset: Size) -> Value {
        Value::Load(Load { src, offset })
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Extract {
    pub src: Variable,
    pub index: usize,
}

LirImplInto!(Value for Extract);

impl Display for Extract {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "extract {} index=({})", self.src, self.index)
    }
}

impl<'a> GetLocalsMut<'a> for Extract {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.src.get_locals_mut()
    }
}

impl<'a> GetLocals<'a> for Extract {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.src.get_locals()
    }
}

impl Substitutable for Extract {
    fn apply_subst(&mut self, subst: &Subst) {
        self.src.apply_subst(subst);
    }
}

impl Extract {
    pub fn new(src: Variable, index: usize) -> Value {
        Value::Extract(Extract { src, index })
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Insert {
    pub src: Variable,
    pub index: usize,
    pub value: Value,
}

impl Display for Insert {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "insert {} index=({}) value={}",
            self.src, self.index, self.value
        )
    }
}

impl<'a> GetLocalsMut<'a> for Insert {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        let mut locs = self.src.get_locals_mut();
        locs.extend(self.value.get_locals_mut());
        locs
    }
}

impl<'a> GetLocals<'a> for Insert {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        let mut locs = self.src.get_locals();
        locs.extend(self.value.get_locals());
        locs
    }
}

impl Substitutable for Insert {
    fn apply_subst(&mut self, subst: &Subst) {
        self.src.apply_subst(subst);
        self.value.apply_subst(subst);
    }
}

impl Insert {
    pub fn new(src: Variable, index: usize, value: Value) -> Insert {
        Insert { src, index, value }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum LeaOffset {
    Const(Size),
    Field(TyScheme, String),
}

impl Display for LeaOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LeaOffset::Const(size) => write!(f, "{}", size),
            LeaOffset::Field(ty_scheme, field) => write!(f, "offset-of({}::{})", ty_scheme, field),
        }
    }
}

impl Substitutable for LeaOffset {
    fn apply_subst(&mut self, subst: &Subst) {
        match self {
            LeaOffset::Const(_) => {}
            LeaOffset::Field(ty_scheme, _) => ty_scheme.apply_subst(subst),
        }
    }
}

impl LeaOffset {
    pub fn zero() -> LeaOffset {
        LeaOffset::Const(Size::zero())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Lea {
    /// Variable to load address of
    pub var: Variable,

    /// Effective byte/ptr offset from `value`
    pub offset: LeaOffset,
}

LirImplInto!(Value for Lea);

impl Display for Lea {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "lea {} {}", self.var, self.offset)
    }
}

impl<'a> GetLocalsMut<'a> for Lea {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.var.get_locals_mut()
    }
}

impl<'a> GetLocals<'a> for Lea {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.var.get_locals()
    }
}

impl Substitutable for Lea {
    fn apply_subst(&mut self, subst: &Subst) {
        self.var.apply_subst(subst);
        self.offset.apply_subst(subst);
    }
}

impl Lea {
    pub fn new(var: Variable, offset: LeaOffset) -> Value {
        Value::Lea(Self { var, offset })
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GetField {
    pub src: Variable,
    pub field: String,
}

LirImplInto!(Value for GetField);

impl Display for GetField {
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

impl Substitutable for GetField {
    fn apply_subst(&mut self, subst: &Subst) {
        self.src.apply_subst(subst);
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SetField {
    pub dst: Variable,
    pub field: String,
    pub value: Value,
}

impl Display for SetField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "setfield {} {} {}", self.dst, self.field, self.value,)
    }
}

impl<'a> GetLocalsMut<'a> for SetField {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        let mut locs = self.dst.get_locals_mut();
        locs.extend(self.value.get_locals_mut());
        locs
    }
}

impl<'a> GetLocals<'a> for SetField {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        let mut locs = self.dst.get_locals();
        locs.extend(self.value.get_locals());
        locs
    }
}

impl Substitutable for SetField {
    fn apply_subst(&mut self, subst: &Subst) {
        self.dst.apply_subst(subst);
        self.value.apply_subst(subst);
    }
}

impl SetField {
    pub fn new(dst: Variable, field: String, value: Value) -> Inst {
        Inst::SetField(SetField { dst, field, value })
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BasicOp {
    pub op: Op,
    pub size: Size,
    pub signed: bool,
    pub operands: Vec<Atom>,
}

LirImplInto!(Value for BasicOp);

impl Display for BasicOp {
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

impl Substitutable for BasicOp {
    fn apply_subst(&mut self, subst: &Subst) {
        self.operands.apply_subst(subst);
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Cast {
    pub src: Variable,
    pub ty: Ty,
}

LirImplInto!(Value for Cast);

impl Cast {
    pub fn new(src: Variable, ty: Ty) -> Value {
        Value::Cast(Cast { src, ty })
    }
}

impl Display for Cast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} as {}", self.src, self.ty)
    }
}

impl<'a> GetLocalsMut<'a> for Cast {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.src.get_locals_mut()
    }
}

impl<'a> GetLocals<'a> for Cast {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.src.get_locals()
    }
}

impl Substitutable for Cast {
    fn apply_subst(&mut self, subst: &Subst) {
        self.src.apply_subst(subst);
        self.ty.apply_subst(subst);
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct IntConvert {
    value: Atom,
    src: (Size, bool),
    dst: (Size, bool),
}

LirImplInto!(Value for IntConvert);

impl Display for IntConvert {
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

impl Substitutable for IntConvert {
    fn apply_subst(&mut self, subst: &Subst) {
        self.value.apply_subst(subst);
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Closure {
    pub handle: StructTy,
    pub fn_name: Path,
    pub fn_ty: TyScheme,
    pub poly_ty: Option<TyScheme>,
    pub env: Variable,
}

LirImplInto!(Value for Closure);

impl Closure {
    pub fn new(
        handle: StructTy,
        fn_name: Path,
        fn_ty: TyScheme,
        poly_ty: Option<TyScheme>,
        env: Variable,
    ) -> Self {
        Self {
            handle,
            fn_name,
            fn_ty,
            poly_ty,
            env,
        }
    }
}

impl<'a> GetLocals<'a> for Closure {
    fn get_locals(&'a self) -> Vec<&'a usize> {
        self.env.get_locals()
    }
}

impl<'a> GetLocalsMut<'a> for Closure {
    fn get_locals_mut(&'a mut self) -> Vec<&'a mut usize> {
        self.env.get_locals_mut()
    }
}

impl Substitutable for Closure {
    fn apply_subst(&mut self, subst: &Subst) {
        self.handle.apply_subst(subst);
        self.fn_name.apply_subst(subst);
        self.fn_ty.apply_subst(subst);
        if let Some(poly) = &mut self.poly_ty {
            poly.apply_subst(subst);
        }
        self.env.apply_subst(subst);
    }
}

#[derive(Clone)]
pub struct CaptureSlot {
    pub binding: LocalBindingId,
    pub ty: TyScheme,
    pub value: Variable,
}

impl CaptureSlot {
    pub fn id(&self) -> String {
        format!("%__capture_{:x}", self.binding)
    }
}

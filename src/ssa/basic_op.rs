use crate::ast;

use super::{Size, Value};

#[derive(Copy, Clone, Debug)]
pub enum BasicOpKind {
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

impl std::fmt::Display for BasicOpKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BasicOpKind::Malloc => write!(f, "malloc"),
            BasicOpKind::Add => write!(f, "add"),
            BasicOpKind::Sub => write!(f, "sub"),
            BasicOpKind::Mul => write!(f, "mul"),
            BasicOpKind::Div => write!(f, "div"),
            BasicOpKind::Mod => write!(f, "mod"),
            BasicOpKind::BitXor => write!(f, "xor"),
            BasicOpKind::BitAnd => write!(f, "bitand"),
            BasicOpKind::BitOr => write!(f, "bitor"),
            BasicOpKind::BitNot => write!(f, "bitnot"),
            BasicOpKind::ArithShiftLeft => write!(f, "asl"),
            BasicOpKind::ArithShiftRight => write!(f, "asr"),
            BasicOpKind::LogicalShiftLeft => write!(f, "lsl"),
            BasicOpKind::LogicalShiftRight => write!(f, "lsr"),
            BasicOpKind::RotateLeft => write!(f, "rotl"),
            BasicOpKind::RotateRight => write!(f, "rotr"),
            BasicOpKind::Lt => write!(f, "lt"),
            BasicOpKind::LtEq => write!(f, "lteq"),
            BasicOpKind::Gt => write!(f, "gt"),
            BasicOpKind::GtEq => write!(f, "gteq"),
            BasicOpKind::Eq => write!(f, "eq"),
            BasicOpKind::Neq => write!(f, "neq"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct BasicOp {
    pub op: BasicOpKind,
    pub size: Size,
    pub signed: bool,
    pub operands: Vec<Value>,
}

impl std::fmt::Display for BasicOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let operands = crate::utils::join(&self.operands, " ");
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

impl From<ast::asm::AsmOp> for BasicOp {
    fn from(op: ast::asm::AsmOp) -> Self {
        match op {
            ast::asm::AsmOp::Malloc => unreachable!(),
            ast::asm::AsmOp::ISizeEq => BasicOp {
                op: BasicOpKind::Eq,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Eq => BasicOp {
                op: BasicOpKind::Eq,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Eq => BasicOp {
                op: BasicOpKind::Eq,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Eq => BasicOp {
                op: BasicOpKind::Eq,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Eq => BasicOp {
                op: BasicOpKind::Eq,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeEq => BasicOp {
                op: BasicOpKind::Eq,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Eq => BasicOp {
                op: BasicOpKind::Eq,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Eq => BasicOp {
                op: BasicOpKind::Eq,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Eq => BasicOp {
                op: BasicOpKind::Eq,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Eq => BasicOp {
                op: BasicOpKind::Eq,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeNeq => BasicOp {
                op: BasicOpKind::Neq,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Neq => BasicOp {
                op: BasicOpKind::Neq,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Neq => BasicOp {
                op: BasicOpKind::Neq,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Neq => BasicOp {
                op: BasicOpKind::Neq,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Neq => BasicOp {
                op: BasicOpKind::Neq,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeNeq => BasicOp {
                op: BasicOpKind::Neq,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Neq => BasicOp {
                op: BasicOpKind::Neq,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Neq => BasicOp {
                op: BasicOpKind::Neq,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Neq => BasicOp {
                op: BasicOpKind::Neq,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Neq => BasicOp {
                op: BasicOpKind::Neq,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeAdd => BasicOp {
                op: BasicOpKind::Add,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Add => BasicOp {
                op: BasicOpKind::Add,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Add => BasicOp {
                op: BasicOpKind::Add,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Add => BasicOp {
                op: BasicOpKind::Add,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Add => BasicOp {
                op: BasicOpKind::Add,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeAdd => BasicOp {
                op: BasicOpKind::Add,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Add => BasicOp {
                op: BasicOpKind::Add,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Add => BasicOp {
                op: BasicOpKind::Add,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Add => BasicOp {
                op: BasicOpKind::Add,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Add => BasicOp {
                op: BasicOpKind::Add,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeSub => BasicOp {
                op: BasicOpKind::Sub,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Sub => BasicOp {
                op: BasicOpKind::Sub,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Sub => BasicOp {
                op: BasicOpKind::Sub,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Sub => BasicOp {
                op: BasicOpKind::Sub,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Sub => BasicOp {
                op: BasicOpKind::Sub,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeSub => BasicOp {
                op: BasicOpKind::Sub,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Sub => BasicOp {
                op: BasicOpKind::Sub,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Sub => BasicOp {
                op: BasicOpKind::Sub,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Sub => BasicOp {
                op: BasicOpKind::Sub,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Sub => BasicOp {
                op: BasicOpKind::Sub,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeMul => BasicOp {
                op: BasicOpKind::Mul,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Mul => BasicOp {
                op: BasicOpKind::Mul,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Mul => BasicOp {
                op: BasicOpKind::Mul,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Mul => BasicOp {
                op: BasicOpKind::Mul,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Mul => BasicOp {
                op: BasicOpKind::Mul,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeMul => BasicOp {
                op: BasicOpKind::Mul,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Mul => BasicOp {
                op: BasicOpKind::Mul,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Mul => BasicOp {
                op: BasicOpKind::Mul,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Mul => BasicOp {
                op: BasicOpKind::Mul,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Mul => BasicOp {
                op: BasicOpKind::Mul,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeDiv => BasicOp {
                op: BasicOpKind::Div,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Div => BasicOp {
                op: BasicOpKind::Div,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Div => BasicOp {
                op: BasicOpKind::Div,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Div => BasicOp {
                op: BasicOpKind::Div,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Div => BasicOp {
                op: BasicOpKind::Div,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeDiv => BasicOp {
                op: BasicOpKind::Div,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Div => BasicOp {
                op: BasicOpKind::Div,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Div => BasicOp {
                op: BasicOpKind::Div,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Div => BasicOp {
                op: BasicOpKind::Div,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Div => BasicOp {
                op: BasicOpKind::Div,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeMod => BasicOp {
                op: BasicOpKind::Mod,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Mod => BasicOp {
                op: BasicOpKind::Mod,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Mod => BasicOp {
                op: BasicOpKind::Mod,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Mod => BasicOp {
                op: BasicOpKind::Mod,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Mod => BasicOp {
                op: BasicOpKind::Mod,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeMod => BasicOp {
                op: BasicOpKind::Mod,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Mod => BasicOp {
                op: BasicOpKind::Mod,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Mod => BasicOp {
                op: BasicOpKind::Mod,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Mod => BasicOp {
                op: BasicOpKind::Mod,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Mod => BasicOp {
                op: BasicOpKind::Mod,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeAnd => BasicOp {
                op: BasicOpKind::BitAnd,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8And => BasicOp {
                op: BasicOpKind::BitAnd,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16And => BasicOp {
                op: BasicOpKind::BitAnd,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32And => BasicOp {
                op: BasicOpKind::BitAnd,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64And => BasicOp {
                op: BasicOpKind::BitAnd,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeAnd => BasicOp {
                op: BasicOpKind::BitAnd,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8And => BasicOp {
                op: BasicOpKind::BitAnd,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16And => BasicOp {
                op: BasicOpKind::BitAnd,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32And => BasicOp {
                op: BasicOpKind::BitAnd,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64And => BasicOp {
                op: BasicOpKind::BitAnd,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeOr => BasicOp {
                op: BasicOpKind::BitOr,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Or => BasicOp {
                op: BasicOpKind::BitOr,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Or => BasicOp {
                op: BasicOpKind::BitOr,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Or => BasicOp {
                op: BasicOpKind::BitOr,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Or => BasicOp {
                op: BasicOpKind::BitOr,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeOr => BasicOp {
                op: BasicOpKind::BitOr,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Or => BasicOp {
                op: BasicOpKind::BitOr,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Or => BasicOp {
                op: BasicOpKind::BitOr,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Or => BasicOp {
                op: BasicOpKind::BitOr,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Or => BasicOp {
                op: BasicOpKind::BitOr,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeXor => BasicOp {
                op: BasicOpKind::BitXor,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Xor => BasicOp {
                op: BasicOpKind::BitXor,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Xor => BasicOp {
                op: BasicOpKind::BitXor,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Xor => BasicOp {
                op: BasicOpKind::BitXor,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Xor => BasicOp {
                op: BasicOpKind::BitXor,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeXor => BasicOp {
                op: BasicOpKind::BitXor,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Xor => BasicOp {
                op: BasicOpKind::BitXor,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Xor => BasicOp {
                op: BasicOpKind::BitXor,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Xor => BasicOp {
                op: BasicOpKind::BitXor,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Xor => BasicOp {
                op: BasicOpKind::BitXor,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeLt => BasicOp {
                op: BasicOpKind::Lt,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Lt => BasicOp {
                op: BasicOpKind::Lt,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Lt => BasicOp {
                op: BasicOpKind::Lt,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Lt => BasicOp {
                op: BasicOpKind::Lt,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Lt => BasicOp {
                op: BasicOpKind::Lt,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeLt => BasicOp {
                op: BasicOpKind::Lt,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Lt => BasicOp {
                op: BasicOpKind::Lt,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Lt => BasicOp {
                op: BasicOpKind::Lt,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Lt => BasicOp {
                op: BasicOpKind::Lt,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Lt => BasicOp {
                op: BasicOpKind::Lt,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeGt => BasicOp {
                op: BasicOpKind::Gt,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Gt => BasicOp {
                op: BasicOpKind::Gt,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Gt => BasicOp {
                op: BasicOpKind::Gt,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Gt => BasicOp {
                op: BasicOpKind::Gt,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Gt => BasicOp {
                op: BasicOpKind::Gt,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeGt => BasicOp {
                op: BasicOpKind::Gt,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Gt => BasicOp {
                op: BasicOpKind::Gt,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Gt => BasicOp {
                op: BasicOpKind::Gt,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Gt => BasicOp {
                op: BasicOpKind::Gt,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Gt => BasicOp {
                op: BasicOpKind::Gt,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeLtEq => BasicOp {
                op: BasicOpKind::LtEq,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8LtEq => BasicOp {
                op: BasicOpKind::LtEq,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16LtEq => BasicOp {
                op: BasicOpKind::LtEq,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32LtEq => BasicOp {
                op: BasicOpKind::LtEq,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64LtEq => BasicOp {
                op: BasicOpKind::LtEq,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeLtEq => BasicOp {
                op: BasicOpKind::LtEq,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8LtEq => BasicOp {
                op: BasicOpKind::LtEq,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16LtEq => BasicOp {
                op: BasicOpKind::LtEq,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32LtEq => BasicOp {
                op: BasicOpKind::LtEq,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64LtEq => BasicOp {
                op: BasicOpKind::LtEq,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeGtEq => BasicOp {
                op: BasicOpKind::GtEq,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8GtEq => BasicOp {
                op: BasicOpKind::GtEq,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16GtEq => BasicOp {
                op: BasicOpKind::GtEq,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32GtEq => BasicOp {
                op: BasicOpKind::GtEq,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64GtEq => BasicOp {
                op: BasicOpKind::GtEq,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeGtEq => BasicOp {
                op: BasicOpKind::GtEq,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8GtEq => BasicOp {
                op: BasicOpKind::GtEq,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16GtEq => BasicOp {
                op: BasicOpKind::GtEq,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32GtEq => BasicOp {
                op: BasicOpKind::GtEq,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64GtEq => BasicOp {
                op: BasicOpKind::GtEq,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeShl => BasicOp {
                op: BasicOpKind::ArithShiftLeft,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Shl => BasicOp {
                op: BasicOpKind::ArithShiftLeft,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Shl => BasicOp {
                op: BasicOpKind::ArithShiftLeft,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Shl => BasicOp {
                op: BasicOpKind::ArithShiftLeft,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Shl => BasicOp {
                op: BasicOpKind::ArithShiftLeft,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeShl => BasicOp {
                op: BasicOpKind::ArithShiftLeft,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Shl => BasicOp {
                op: BasicOpKind::ArithShiftLeft,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Shl => BasicOp {
                op: BasicOpKind::ArithShiftLeft,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Shl => BasicOp {
                op: BasicOpKind::ArithShiftLeft,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Shl => BasicOp {
                op: BasicOpKind::ArithShiftLeft,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeShr => BasicOp {
                op: BasicOpKind::ArithShiftRight,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Shr => BasicOp {
                op: BasicOpKind::ArithShiftRight,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Shr => BasicOp {
                op: BasicOpKind::ArithShiftRight,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Shr => BasicOp {
                op: BasicOpKind::ArithShiftRight,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Shr => BasicOp {
                op: BasicOpKind::ArithShiftRight,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeShr => BasicOp {
                op: BasicOpKind::ArithShiftRight,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Shr => BasicOp {
                op: BasicOpKind::ArithShiftRight,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Shr => BasicOp {
                op: BasicOpKind::ArithShiftRight,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Shr => BasicOp {
                op: BasicOpKind::ArithShiftRight,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Shr => BasicOp {
                op: BasicOpKind::ArithShiftRight,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeRotl => BasicOp {
                op: BasicOpKind::RotateLeft,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Rotl => BasicOp {
                op: BasicOpKind::RotateLeft,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Rotl => BasicOp {
                op: BasicOpKind::RotateLeft,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Rotl => BasicOp {
                op: BasicOpKind::RotateLeft,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Rotl => BasicOp {
                op: BasicOpKind::RotateLeft,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeRotl => BasicOp {
                op: BasicOpKind::RotateLeft,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Rotl => BasicOp {
                op: BasicOpKind::RotateLeft,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Rotl => BasicOp {
                op: BasicOpKind::RotateLeft,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Rotl => BasicOp {
                op: BasicOpKind::RotateLeft,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Rotl => BasicOp {
                op: BasicOpKind::RotateLeft,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::ISizeRotr => BasicOp {
                op: BasicOpKind::RotateRight,
                size: Size::ptr(),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I8Rotr => BasicOp {
                op: BasicOpKind::RotateRight,
                size: Size::bytes(1),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I16Rotr => BasicOp {
                op: BasicOpKind::RotateRight,
                size: Size::bytes(2),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I32Rotr => BasicOp {
                op: BasicOpKind::RotateRight,
                size: Size::bytes(4),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::I64Rotr => BasicOp {
                op: BasicOpKind::RotateRight,
                size: Size::bytes(8),
                signed: true,
                operands: vec![],
            },
            ast::asm::AsmOp::USizeRotr => BasicOp {
                op: BasicOpKind::RotateRight,
                size: Size::ptr(),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U8Rotr => BasicOp {
                op: BasicOpKind::RotateRight,
                size: Size::bytes(1),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U16Rotr => BasicOp {
                op: BasicOpKind::RotateRight,
                size: Size::bytes(2),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U32Rotr => BasicOp {
                op: BasicOpKind::RotateRight,
                size: Size::bytes(4),
                signed: false,
                operands: vec![],
            },
            ast::asm::AsmOp::U64Rotr => BasicOp {
                op: BasicOpKind::RotateRight,
                size: Size::bytes(8),
                signed: false,
                operands: vec![],
            },
        }
    }
}

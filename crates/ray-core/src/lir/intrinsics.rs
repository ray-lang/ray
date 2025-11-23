use serde::{Deserialize, Serialize};

use ray_shared::pathlib::Path;

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum IntrinsicKind {
    PtrAdd,
    PtrSub,
    DerefRef,
    DerefRaw,
    SizeOf,
    Memcopy,
    IntEq,
    I8Eq,
    I16Eq,
    I32Eq,
    I64Eq,
    UintEq,
    U8Eq,
    U16Eq,
    U32Eq,
    U64Eq,
    IntNeq,
    I8Neq,
    I16Neq,
    I32Neq,
    I64Neq,
    UintNeq,
    U8Neq,
    U16Neq,
    U32Neq,
    U64Neq,
    IntAdd,
    I8Add,
    I16Add,
    I32Add,
    I64Add,
    UintAdd,
    U8Add,
    U16Add,
    U32Add,
    U64Add,
    IntSub,
    I8Sub,
    I16Sub,
    I32Sub,
    I64Sub,
    UintSub,
    U8Sub,
    U16Sub,
    U32Sub,
    U64Sub,
    IntMul,
    I8Mul,
    I16Mul,
    I32Mul,
    I64Mul,
    UintMul,
    U8Mul,
    U16Mul,
    U32Mul,
    U64Mul,
    IntDiv,
    I8Div,
    I16Div,
    I32Div,
    I64Div,
    UintDiv,
    U8Div,
    U16Div,
    U32Div,
    U64Div,
    IntMod,
    I8Mod,
    I16Mod,
    I32Mod,
    I64Mod,
    UintMod,
    U8Mod,
    U16Mod,
    U32Mod,
    U64Mod,
    IntNeg,
    I8Neg,
    I16Neg,
    I32Neg,
    I64Neg,
    IntAnd,
    I8And,
    I16And,
    I32And,
    I64And,
    UintAnd,
    U8And,
    U16And,
    U32And,
    U64And,
    IntOr,
    I8Or,
    I16Or,
    I32Or,
    I64Or,
    UintOr,
    U8Or,
    U16Or,
    U32Or,
    U64Or,
    IntXor,
    I8Xor,
    I16Xor,
    I32Xor,
    I64Xor,
    UintXor,
    U8Xor,
    U16Xor,
    U32Xor,
    U64Xor,
    IntLt,
    I8Lt,
    I16Lt,
    I32Lt,
    I64Lt,
    UintLt,
    U8Lt,
    U16Lt,
    U32Lt,
    U64Lt,
    IntGt,
    I8Gt,
    I16Gt,
    I32Gt,
    I64Gt,
    UintGt,
    U8Gt,
    U16Gt,
    U32Gt,
    U64Gt,
    IntLteq,
    I8Lteq,
    I16Lteq,
    I32Lteq,
    I64Lteq,
    UintLteq,
    U8Lteq,
    U16Lteq,
    U32Lteq,
    U64Lteq,
    IntGteq,
    I8Gteq,
    I16Gteq,
    I32Gteq,
    I64Gteq,
    UintGteq,
    U8Gteq,
    U16Gteq,
    U32Gteq,
    U64Gteq,
    IntShl,
    I8Shl,
    I16Shl,
    I32Shl,
    I64Shl,
    UintShl,
    U8Shl,
    U16Shl,
    U32Shl,
    U64Shl,
    IntShr,
    I8Shr,
    I16Shr,
    I32Shr,
    I64Shr,
    UintShr,
    U8Shr,
    U16Shr,
    U32Shr,
    U64Shr,
    IntRotl,
    I8Rotl,
    I16Rotl,
    I32Rotl,
    I64Rotl,
    UintRotl,
    U8Rotl,
    U16Rotl,
    U32Rotl,
    U64Rotl,
    IntRotr,
    I8Rotr,
    I16Rotr,
    I32Rotr,
    I64Rotr,
    UintRotr,
    U8Rotr,
    U16Rotr,
    U32Rotr,
    U64Rotr,
}

impl IntrinsicKind {
    pub fn from_path(path: &Path) -> Option<Self> {
        match path.to_short_name().as_str() {
            "__ptr_add" => Some(Self::PtrAdd),
            "__ptr_sub" => Some(Self::PtrSub),
            "__deref_ref" => Some(Self::DerefRef),
            "__deref_raw" => Some(Self::DerefRaw),
            "sizeof" => Some(Self::SizeOf),
            "memcopy" => Some(Self::Memcopy),
            "int_eq" => Some(Self::IntEq),
            "i8_eq" => Some(Self::I8Eq),
            "i16_eq" => Some(Self::I16Eq),
            "i32_eq" => Some(Self::I32Eq),
            "i64_eq" => Some(Self::I64Eq),
            "uint_eq" => Some(Self::UintEq),
            "u8_eq" => Some(Self::U8Eq),
            "u16_eq" => Some(Self::U16Eq),
            "u32_eq" => Some(Self::U32Eq),
            "u64_eq" => Some(Self::U64Eq),
            "int_neq" => Some(Self::IntNeq),
            "i8_neq" => Some(Self::I8Neq),
            "i16_neq" => Some(Self::I16Neq),
            "i32_neq" => Some(Self::I32Neq),
            "i64_neq" => Some(Self::I64Neq),
            "uint_neq" => Some(Self::UintNeq),
            "u8_neq" => Some(Self::U8Neq),
            "u16_neq" => Some(Self::U16Neq),
            "u32_neq" => Some(Self::U32Neq),
            "u64_neq" => Some(Self::U64Neq),
            "int_add" => Some(Self::IntAdd),
            "i8_add" => Some(Self::I8Add),
            "i16_add" => Some(Self::I16Add),
            "i32_add" => Some(Self::I32Add),
            "i64_add" => Some(Self::I64Add),
            "uint_add" => Some(Self::UintAdd),
            "u8_add" => Some(Self::U8Add),
            "u16_add" => Some(Self::U16Add),
            "u32_add" => Some(Self::U32Add),
            "u64_add" => Some(Self::U64Add),
            "int_sub" => Some(Self::IntSub),
            "i8_sub" => Some(Self::I8Sub),
            "i16_sub" => Some(Self::I16Sub),
            "i32_sub" => Some(Self::I32Sub),
            "i64_sub" => Some(Self::I64Sub),
            "uint_sub" => Some(Self::UintSub),
            "u8_sub" => Some(Self::U8Sub),
            "u16_sub" => Some(Self::U16Sub),
            "u32_sub" => Some(Self::U32Sub),
            "u64_sub" => Some(Self::U64Sub),
            "int_mul" => Some(Self::IntMul),
            "i8_mul" => Some(Self::I8Mul),
            "i16_mul" => Some(Self::I16Mul),
            "i32_mul" => Some(Self::I32Mul),
            "i64_mul" => Some(Self::I64Mul),
            "uint_mul" => Some(Self::UintMul),
            "u8_mul" => Some(Self::U8Mul),
            "u16_mul" => Some(Self::U16Mul),
            "u32_mul" => Some(Self::U32Mul),
            "u64_mul" => Some(Self::U64Mul),
            "int_div" => Some(Self::IntDiv),
            "i8_div" => Some(Self::I8Div),
            "i16_div" => Some(Self::I16Div),
            "i32_div" => Some(Self::I32Div),
            "i64_div" => Some(Self::I64Div),
            "uint_div" => Some(Self::UintDiv),
            "u8_div" => Some(Self::U8Div),
            "u16_div" => Some(Self::U16Div),
            "u32_div" => Some(Self::U32Div),
            "u64_div" => Some(Self::U64Div),
            "int_mod" => Some(Self::IntMod),
            "i8_mod" => Some(Self::I8Mod),
            "i16_mod" => Some(Self::I16Mod),
            "i32_mod" => Some(Self::I32Mod),
            "i64_mod" => Some(Self::I64Mod),
            "uint_mod" => Some(Self::UintMod),
            "u8_mod" => Some(Self::U8Mod),
            "u16_mod" => Some(Self::U16Mod),
            "u32_mod" => Some(Self::U32Mod),
            "u64_mod" => Some(Self::U64Mod),
            "int_neg" => Some(Self::IntNeg),
            "i8_neg" => Some(Self::I8Neg),
            "i16_neg" => Some(Self::I16Neg),
            "i32_neg" => Some(Self::I32Neg),
            "i64_neg" => Some(Self::I64Neg),
            "int_and" => Some(Self::IntAnd),
            "i8_and" => Some(Self::I8And),
            "i16_and" => Some(Self::I16And),
            "i32_and" => Some(Self::I32And),
            "i64_and" => Some(Self::I64And),
            "uint_and" => Some(Self::UintAnd),
            "u8_and" => Some(Self::U8And),
            "u16_and" => Some(Self::U16And),
            "u32_and" => Some(Self::U32And),
            "u64_and" => Some(Self::U64And),
            "int_or" => Some(Self::IntOr),
            "i8_or" => Some(Self::I8Or),
            "i16_or" => Some(Self::I16Or),
            "i32_or" => Some(Self::I32Or),
            "i64_or" => Some(Self::I64Or),
            "uint_or" => Some(Self::UintOr),
            "u8_or" => Some(Self::U8Or),
            "u16_or" => Some(Self::U16Or),
            "u32_or" => Some(Self::U32Or),
            "u64_or" => Some(Self::U64Or),
            "int_xor" => Some(Self::IntXor),
            "i8_xor" => Some(Self::I8Xor),
            "i16_xor" => Some(Self::I16Xor),
            "i32_xor" => Some(Self::I32Xor),
            "i64_xor" => Some(Self::I64Xor),
            "uint_xor" => Some(Self::UintXor),
            "u8_xor" => Some(Self::U8Xor),
            "u16_xor" => Some(Self::U16Xor),
            "u32_xor" => Some(Self::U32Xor),
            "u64_xor" => Some(Self::U64Xor),
            "int_lt" => Some(Self::IntLt),
            "i8_lt" => Some(Self::I8Lt),
            "i16_lt" => Some(Self::I16Lt),
            "i32_lt" => Some(Self::I32Lt),
            "i64_lt" => Some(Self::I64Lt),
            "uint_lt" => Some(Self::UintLt),
            "u8_lt" => Some(Self::U8Lt),
            "u16_lt" => Some(Self::U16Lt),
            "u32_lt" => Some(Self::U32Lt),
            "u64_lt" => Some(Self::U64Lt),
            "int_gt" => Some(Self::IntGt),
            "i8_gt" => Some(Self::I8Gt),
            "i16_gt" => Some(Self::I16Gt),
            "i32_gt" => Some(Self::I32Gt),
            "i64_gt" => Some(Self::I64Gt),
            "uint_gt" => Some(Self::UintGt),
            "u8_gt" => Some(Self::U8Gt),
            "u16_gt" => Some(Self::U16Gt),
            "u32_gt" => Some(Self::U32Gt),
            "u64_gt" => Some(Self::U64Gt),
            "int_lteq" => Some(Self::IntLteq),
            "i8_lteq" => Some(Self::I8Lteq),
            "i16_lteq" => Some(Self::I16Lteq),
            "i32_lteq" => Some(Self::I32Lteq),
            "i64_lteq" => Some(Self::I64Lteq),
            "uint_lteq" => Some(Self::UintLteq),
            "u8_lteq" => Some(Self::U8Lteq),
            "u16_lteq" => Some(Self::U16Lteq),
            "u32_lteq" => Some(Self::U32Lteq),
            "u64_lteq" => Some(Self::U64Lteq),
            "int_gteq" => Some(Self::IntGteq),
            "i8_gteq" => Some(Self::I8Gteq),
            "i16_gteq" => Some(Self::I16Gteq),
            "i32_gteq" => Some(Self::I32Gteq),
            "i64_gteq" => Some(Self::I64Gteq),
            "uint_gteq" => Some(Self::UintGteq),
            "u8_gteq" => Some(Self::U8Gteq),
            "u16_gteq" => Some(Self::U16Gteq),
            "u32_gteq" => Some(Self::U32Gteq),
            "u64_gteq" => Some(Self::U64Gteq),
            "int_shl" => Some(Self::IntShl),
            "i8_shl" => Some(Self::I8Shl),
            "i16_shl" => Some(Self::I16Shl),
            "i32_shl" => Some(Self::I32Shl),
            "i64_shl" => Some(Self::I64Shl),
            "uint_shl" => Some(Self::UintShl),
            "u8_shl" => Some(Self::U8Shl),
            "u16_shl" => Some(Self::U16Shl),
            "u32_shl" => Some(Self::U32Shl),
            "u64_shl" => Some(Self::U64Shl),
            "int_shr" => Some(Self::IntShr),
            "i8_shr" => Some(Self::I8Shr),
            "i16_shr" => Some(Self::I16Shr),
            "i32_shr" => Some(Self::I32Shr),
            "i64_shr" => Some(Self::I64Shr),
            "uint_shr" => Some(Self::UintShr),
            "u8_shr" => Some(Self::U8Shr),
            "u16_shr" => Some(Self::U16Shr),
            "u32_shr" => Some(Self::U32Shr),
            "u64_shr" => Some(Self::U64Shr),
            "int_rotl" => Some(Self::IntRotl),
            "i8_rotl" => Some(Self::I8Rotl),
            "i16_rotl" => Some(Self::I16Rotl),
            "i32_rotl" => Some(Self::I32Rotl),
            "i64_rotl" => Some(Self::I64Rotl),
            "uint_rotl" => Some(Self::UintRotl),
            "u8_rotl" => Some(Self::U8Rotl),
            "u16_rotl" => Some(Self::U16Rotl),
            "u32_rotl" => Some(Self::U32Rotl),
            "u64_rotl" => Some(Self::U64Rotl),
            "int_rotr" => Some(Self::IntRotr),
            "i8_rotr" => Some(Self::I8Rotr),
            "i16_rotr" => Some(Self::I16Rotr),
            "i32_rotr" => Some(Self::I32Rotr),
            "i64_rotr" => Some(Self::I64Rotr),
            "uint_rotr" => Some(Self::UintRotr),
            "u8_rotr" => Some(Self::U8Rotr),
            "u16_rotr" => Some(Self::U16Rotr),
            "u32_rotr" => Some(Self::U32Rotr),
            "u64_rotr" => Some(Self::U64Rotr),
            _ => None,
        }
    }

    pub fn is_signed(&self) -> bool {
        matches!(
            self,
            Self::IntEq
                | Self::I8Eq
                | Self::I16Eq
                | Self::I32Eq
                | Self::I64Eq
                | Self::IntNeq
                | Self::I8Neq
                | Self::I16Neq
                | Self::I32Neq
                | Self::I64Neq
                | Self::IntAdd
                | Self::I8Add
                | Self::I16Add
                | Self::I32Add
                | Self::I64Add
                | Self::IntSub
                | Self::I8Sub
                | Self::I16Sub
                | Self::I32Sub
                | Self::I64Sub
                | Self::IntMul
                | Self::I8Mul
                | Self::I16Mul
                | Self::I32Mul
                | Self::I64Mul
                | Self::IntDiv
                | Self::I8Div
                | Self::I16Div
                | Self::I32Div
                | Self::I64Div
                | Self::IntMod
                | Self::I8Mod
                | Self::I16Mod
                | Self::I32Mod
                | Self::I64Mod
                | Self::IntNeg
                | Self::I8Neg
                | Self::I16Neg
                | Self::I32Neg
                | Self::I64Neg
                | Self::IntAnd
                | Self::I8And
                | Self::I16And
                | Self::I32And
                | Self::I64And
                | Self::IntOr
                | Self::I8Or
                | Self::I16Or
                | Self::I32Or
                | Self::I64Or
                | Self::IntXor
                | Self::I8Xor
                | Self::I16Xor
                | Self::I32Xor
                | Self::I64Xor
                | Self::IntLt
                | Self::I8Lt
                | Self::I16Lt
                | Self::I32Lt
                | Self::I64Lt
                | Self::IntGt
                | Self::I8Gt
                | Self::I16Gt
                | Self::I32Gt
                | Self::I64Gt
                | Self::IntLteq
                | Self::I8Lteq
                | Self::I16Lteq
                | Self::I32Lteq
                | Self::I64Lteq
                | Self::IntGteq
                | Self::I8Gteq
                | Self::I16Gteq
                | Self::I32Gteq
                | Self::I64Gteq
                | Self::IntShl
                | Self::I8Shl
                | Self::I16Shl
                | Self::I32Shl
                | Self::I64Shl
                | Self::IntShr
                | Self::I8Shr
                | Self::I16Shr
                | Self::I32Shr
                | Self::I64Shr
                | Self::IntRotl
                | Self::I8Rotl
                | Self::I16Rotl
                | Self::I32Rotl
                | Self::I64Rotl
                | Self::IntRotr
                | Self::I8Rotr
                | Self::I16Rotr
                | Self::I32Rotr
                | Self::I64Rotr
        )
    }
}

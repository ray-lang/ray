use std::convert::TryFrom;

use crate::{
    span::parsed::Parsed,
    typing::{
        ty::{Ty, TyVar},
        ApplySubst, Subst,
    },
    utils::{indent, join, map_join},
};

use super::Path;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum AsmOp {
    // memory ops
    Malloc,

    // eq
    ISizeEq,
    I8Eq,
    I16Eq,
    I32Eq,
    I64Eq,
    USizeEq,
    U8Eq,
    U16Eq,
    U32Eq,
    U64Eq,

    // neq
    ISizeNeq,
    I8Neq,
    I16Neq,
    I32Neq,
    I64Neq,
    USizeNeq,
    U8Neq,
    U16Neq,
    U32Neq,
    U64Neq,

    // add
    ISizeAdd,
    I8Add,
    I16Add,
    I32Add,
    I64Add,
    USizeAdd,
    U8Add,
    U16Add,
    U32Add,
    U64Add,

    // sub
    ISizeSub,
    I8Sub,
    I16Sub,
    I32Sub,
    I64Sub,
    USizeSub,
    U8Sub,
    U16Sub,
    U32Sub,
    U64Sub,

    // mul
    ISizeMul,
    I8Mul,
    I16Mul,
    I32Mul,
    I64Mul,
    USizeMul,
    U8Mul,
    U16Mul,
    U32Mul,
    U64Mul,

    // div
    ISizeDiv,
    I8Div,
    I16Div,
    I32Div,
    I64Div,
    USizeDiv,
    U8Div,
    U16Div,
    U32Div,
    U64Div,

    // mod
    ISizeMod,
    I8Mod,
    I16Mod,
    I32Mod,
    I64Mod,
    USizeMod,
    U8Mod,
    U16Mod,
    U32Mod,
    U64Mod,

    // and
    ISizeAnd,
    I8And,
    I16And,
    I32And,
    I64And,
    USizeAnd,
    U8And,
    U16And,
    U32And,
    U64And,

    // or
    ISizeOr,
    I8Or,
    I16Or,
    I32Or,
    I64Or,
    USizeOr,
    U8Or,
    U16Or,
    U32Or,
    U64Or,

    // xor
    ISizeXor,
    I8Xor,
    I16Xor,
    I32Xor,
    I64Xor,
    USizeXor,
    U8Xor,
    U16Xor,
    U32Xor,
    U64Xor,

    // lt
    ISizeLt,
    I8Lt,
    I16Lt,
    I32Lt,
    I64Lt,
    USizeLt,
    U8Lt,
    U16Lt,
    U32Lt,
    U64Lt,

    // gt
    ISizeGt,
    I8Gt,
    I16Gt,
    I32Gt,
    I64Gt,
    USizeGt,
    U8Gt,
    U16Gt,
    U32Gt,
    U64Gt,

    // lteq
    ISizeLtEq,
    I8LtEq,
    I16LtEq,
    I32LtEq,
    I64LtEq,
    USizeLtEq,
    U8LtEq,
    U16LtEq,
    U32LtEq,
    U64LtEq,

    // gteq
    ISizeGtEq,
    I8GtEq,
    I16GtEq,
    I32GtEq,
    I64GtEq,
    USizeGtEq,
    U8GtEq,
    U16GtEq,
    U32GtEq,
    U64GtEq,

    // shl
    ISizeShl,
    I8Shl,
    I16Shl,
    I32Shl,
    I64Shl,
    USizeShl,
    U8Shl,
    U16Shl,
    U32Shl,
    U64Shl,

    // shr
    ISizeShr,
    I8Shr,
    I16Shr,
    I32Shr,
    I64Shr,
    USizeShr,
    U8Shr,
    U16Shr,
    U32Shr,
    U64Shr,

    // rotl
    ISizeRotl,
    I8Rotl,
    I16Rotl,
    I32Rotl,
    I64Rotl,
    USizeRotl,
    U8Rotl,
    U16Rotl,
    U32Rotl,
    U64Rotl,

    // rotr
    ISizeRotr,
    I8Rotr,
    I16Rotr,
    I32Rotr,
    I64Rotr,
    USizeRotr,
    U8Rotr,
    U16Rotr,
    U32Rotr,
    U64Rotr,
}

impl<'a> TryFrom<&'a str> for AsmOp {
    type Error = &'a str;

    fn try_from(s: &'a str) -> Result<AsmOp, &'a str> {
        Ok(match s {
            // memory
            "malloc" => AsmOp::Malloc,

            // eq
            "int_eq" => AsmOp::ISizeEq,
            "i8_eq" => AsmOp::I8Eq,
            "i16_eq" => AsmOp::I16Eq,
            "i32_eq" => AsmOp::I32Eq,
            "i64_eq" => AsmOp::I64Eq,
            "uint_eq" => AsmOp::USizeEq,
            "u8_eq" => AsmOp::U8Eq,
            "u16_eq" => AsmOp::U16Eq,
            "u32_eq" => AsmOp::U32Eq,
            "u64_eq" => AsmOp::U64Eq,

            // neq
            "int_neq" => AsmOp::ISizeNeq,
            "i8_neq" => AsmOp::I8Neq,
            "i16_neq" => AsmOp::I16Neq,
            "i32_neq" => AsmOp::I32Neq,
            "i64_neq" => AsmOp::I64Neq,
            "uint_neq" => AsmOp::USizeNeq,
            "u8_neq" => AsmOp::U8Neq,
            "u16_neq" => AsmOp::U16Neq,
            "u32_neq" => AsmOp::U32Neq,
            "u64_neq" => AsmOp::U64Neq,

            // add
            "int_add" => AsmOp::ISizeAdd,
            "i8_add" => AsmOp::I8Add,
            "i16_add" => AsmOp::I16Add,
            "i32_add" => AsmOp::I32Add,
            "i64_add" => AsmOp::I64Add,
            "uint_add" => AsmOp::USizeAdd,
            "u8_add" => AsmOp::U8Add,
            "u16_add" => AsmOp::U16Add,
            "u32_add" => AsmOp::U32Add,
            "u64_add" => AsmOp::U64Add,

            // sub
            "int_sub" => AsmOp::ISizeSub,
            "i8_sub" => AsmOp::I8Sub,
            "i16_sub" => AsmOp::I16Sub,
            "i32_sub" => AsmOp::I32Sub,
            "i64_sub" => AsmOp::I64Sub,
            "uint_sub" => AsmOp::USizeSub,
            "u8_sub" => AsmOp::U8Sub,
            "u16_sub" => AsmOp::U16Sub,
            "u32_sub" => AsmOp::U32Sub,
            "u64_sub" => AsmOp::U64Sub,

            // mul
            "int_mul" => AsmOp::ISizeMul,
            "i8_mul" => AsmOp::I8Mul,
            "i16_mul" => AsmOp::I16Mul,
            "i32_mul" => AsmOp::I32Mul,
            "i64_mul" => AsmOp::I64Mul,
            "uint_mul" => AsmOp::USizeMul,
            "u8_mul" => AsmOp::U8Mul,
            "u16_mul" => AsmOp::U16Mul,
            "u32_mul" => AsmOp::U32Mul,
            "u64_mul" => AsmOp::U64Mul,

            // div
            "int_div" => AsmOp::ISizeDiv,
            "i8_div" => AsmOp::I8Div,
            "i16_div" => AsmOp::I16Div,
            "i32_div" => AsmOp::I32Div,
            "i64_div" => AsmOp::I64Div,
            "uint_div" => AsmOp::USizeDiv,
            "u8_div" => AsmOp::U8Div,
            "u16_div" => AsmOp::U16Div,
            "u32_div" => AsmOp::U32Div,
            "u64_div" => AsmOp::U64Div,

            // mod
            "int_mod" => AsmOp::ISizeMod,
            "i8_mod" => AsmOp::I8Mod,
            "i16_mod" => AsmOp::I16Mod,
            "i32_mod" => AsmOp::I32Mod,
            "i64_mod" => AsmOp::I64Mod,
            "uint_mod" => AsmOp::USizeMod,
            "u8_mod" => AsmOp::U8Mod,
            "u16_mod" => AsmOp::U16Mod,
            "u32_mod" => AsmOp::U32Mod,
            "u64_mod" => AsmOp::U64Mod,

            // and
            "int_and" => AsmOp::ISizeAnd,
            "i8_and" => AsmOp::I8And,
            "i16_and" => AsmOp::I16And,
            "i32_and" => AsmOp::I32And,
            "i64_and" => AsmOp::I64And,
            "uint_and" => AsmOp::USizeAnd,
            "u8_and" => AsmOp::U8And,
            "u16_and" => AsmOp::U16And,
            "u32_and" => AsmOp::U32And,
            "u64_and" => AsmOp::U64And,

            // or
            "int_or" => AsmOp::ISizeOr,
            "i8_or" => AsmOp::I8Or,
            "i16_or" => AsmOp::I16Or,
            "i32_or" => AsmOp::I32Or,
            "i64_or" => AsmOp::I64Or,
            "uint_or" => AsmOp::USizeOr,
            "u8_or" => AsmOp::U8Or,
            "u16_or" => AsmOp::U16Or,
            "u32_or" => AsmOp::U32Or,
            "u64_or" => AsmOp::U64Or,

            // xor
            "int_xor" => AsmOp::ISizeXor,
            "i8_xor" => AsmOp::I8Xor,
            "i16_xor" => AsmOp::I16Xor,
            "i32_xor" => AsmOp::I32Xor,
            "i64_xor" => AsmOp::I64Xor,
            "uint_xor" => AsmOp::USizeXor,
            "u8_xor" => AsmOp::U8Xor,
            "u16_xor" => AsmOp::U16Xor,
            "u32_xor" => AsmOp::U32Xor,
            "u64_xor" => AsmOp::U64Xor,

            // lt
            "int_lt" => AsmOp::ISizeLt,
            "i8_lt" => AsmOp::I8Lt,
            "i16_lt" => AsmOp::I16Lt,
            "i32_lt" => AsmOp::I32Lt,
            "i64_lt" => AsmOp::I64Lt,
            "uint_lt" => AsmOp::USizeLt,
            "u8_lt" => AsmOp::U8Lt,
            "u16_lt" => AsmOp::U16Lt,
            "u32_lt" => AsmOp::U32Lt,
            "u64_lt" => AsmOp::U64Lt,

            // gt
            "int_gt" => AsmOp::ISizeGt,
            "i8_gt" => AsmOp::I8Gt,
            "i16_gt" => AsmOp::I16Gt,
            "i32_gt" => AsmOp::I32Gt,
            "i64_gt" => AsmOp::I64Gt,
            "uint_gt" => AsmOp::USizeGt,
            "u8_gt" => AsmOp::U8Gt,
            "u16_gt" => AsmOp::U16Gt,
            "u32_gt" => AsmOp::U32Gt,
            "u64_gt" => AsmOp::U64Gt,

            // lteq
            "int_lteq" => AsmOp::ISizeLtEq,
            "i8_lteq" => AsmOp::I8LtEq,
            "i16_lteq" => AsmOp::I16LtEq,
            "i32_lteq" => AsmOp::I32LtEq,
            "i64_lteq" => AsmOp::I64LtEq,
            "uint_lteq" => AsmOp::USizeLtEq,
            "u8_lteq" => AsmOp::U8LtEq,
            "u16_lteq" => AsmOp::U16LtEq,
            "u32_lteq" => AsmOp::U32LtEq,
            "u64_lteq" => AsmOp::U64LtEq,

            // gteq
            "int_gteq" => AsmOp::ISizeGtEq,
            "i8_gteq" => AsmOp::I8GtEq,
            "i16_gteq" => AsmOp::I16GtEq,
            "i32_gteq" => AsmOp::I32GtEq,
            "i64_gteq" => AsmOp::I64GtEq,
            "uint_gteq" => AsmOp::USizeGtEq,
            "u8_gteq" => AsmOp::U8GtEq,
            "u16_gteq" => AsmOp::U16GtEq,
            "u32_gteq" => AsmOp::U32GtEq,
            "u64_gteq" => AsmOp::U64GtEq,

            // shl
            "int_shl" => AsmOp::ISizeShl,
            "i8_shl" => AsmOp::I8Shl,
            "i16_shl" => AsmOp::I16Shl,
            "i32_shl" => AsmOp::I32Shl,
            "i64_shl" => AsmOp::I64Shl,
            "uint_shl" => AsmOp::USizeShl,
            "u8_shl" => AsmOp::U8Shl,
            "u16_shl" => AsmOp::U16Shl,
            "u32_shl" => AsmOp::U32Shl,
            "u64_shl" => AsmOp::U64Shl,

            // shr
            "int_shr" => AsmOp::ISizeShr,
            "i8_shr" => AsmOp::I8Shr,
            "i16_shr" => AsmOp::I16Shr,
            "i32_shr" => AsmOp::I32Shr,
            "i64_shr" => AsmOp::I64Shr,
            "uint_shr" => AsmOp::USizeShr,
            "u8_shr" => AsmOp::U8Shr,
            "u16_shr" => AsmOp::U16Shr,
            "u32_shr" => AsmOp::U32Shr,
            "u64_shr" => AsmOp::U64Shr,

            // rotl
            "int_rotl" => AsmOp::ISizeRotl,
            "i8_rotl" => AsmOp::I8Rotl,
            "i16_rotl" => AsmOp::I16Rotl,
            "i32_rotl" => AsmOp::I32Rotl,
            "i64_rotl" => AsmOp::I64Rotl,
            "uint_rotl" => AsmOp::USizeRotl,
            "u8_rotl" => AsmOp::U8Rotl,
            "u16_rotl" => AsmOp::U16Rotl,
            "u32_rotl" => AsmOp::U32Rotl,
            "u64_rotl" => AsmOp::U64Rotl,

            // rotr
            "int_rotr" => AsmOp::ISizeRotr,
            "i8_rotr" => AsmOp::I8Rotr,
            "i16_rotr" => AsmOp::I16Rotr,
            "i32_rotr" => AsmOp::I32Rotr,
            "i64_rotr" => AsmOp::I64Rotr,
            "uint_rotr" => AsmOp::USizeRotr,
            "u8_rotr" => AsmOp::U8Rotr,
            "u16_rotr" => AsmOp::U16Rotr,
            "u32_rotr" => AsmOp::U32Rotr,
            "u64_rotr" => AsmOp::U64Rotr,

            s => return Err(s),
        })
    }
}

impl std::fmt::Display for AsmOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            AsmOp::Malloc => "malloc",
            AsmOp::ISizeEq => "int_eq",
            AsmOp::I8Eq => "i8_eq",
            AsmOp::I16Eq => "i16_eq",
            AsmOp::I32Eq => "i32_eq",
            AsmOp::I64Eq => "i64_eq",
            AsmOp::USizeEq => "uint_eq",
            AsmOp::U8Eq => "u8_eq",
            AsmOp::U16Eq => "u16_eq",
            AsmOp::U32Eq => "u32_eq",
            AsmOp::U64Eq => "u64_eq",
            AsmOp::ISizeNeq => "int_neq",
            AsmOp::I8Neq => "i8_neq",
            AsmOp::I16Neq => "i16_neq",
            AsmOp::I32Neq => "i32_neq",
            AsmOp::I64Neq => "i64_neq",
            AsmOp::USizeNeq => "uint_neq",
            AsmOp::U8Neq => "u8_neq",
            AsmOp::U16Neq => "u16_neq",
            AsmOp::U32Neq => "u32_neq",
            AsmOp::U64Neq => "u64_neq",
            AsmOp::ISizeAdd => "int_add",
            AsmOp::I8Add => "i8_add",
            AsmOp::I16Add => "i16_add",
            AsmOp::I32Add => "i32_add",
            AsmOp::I64Add => "i64_add",
            AsmOp::USizeAdd => "uint_add",
            AsmOp::U8Add => "u8_add",
            AsmOp::U16Add => "u16_add",
            AsmOp::U32Add => "u32_add",
            AsmOp::U64Add => "u64_add",
            AsmOp::ISizeSub => "int_sub",
            AsmOp::I8Sub => "i8_sub",
            AsmOp::I16Sub => "i16_sub",
            AsmOp::I32Sub => "i32_sub",
            AsmOp::I64Sub => "i64_sub",
            AsmOp::USizeSub => "uint_sub",
            AsmOp::U8Sub => "u8_sub",
            AsmOp::U16Sub => "u16_sub",
            AsmOp::U32Sub => "u32_sub",
            AsmOp::U64Sub => "u64_sub",
            AsmOp::ISizeMul => "int_mul",
            AsmOp::I8Mul => "i8_mul",
            AsmOp::I16Mul => "i16_mul",
            AsmOp::I32Mul => "i32_mul",
            AsmOp::I64Mul => "i64_mul",
            AsmOp::USizeMul => "uint_mul",
            AsmOp::U8Mul => "u8_mul",
            AsmOp::U16Mul => "u16_mul",
            AsmOp::U32Mul => "u32_mul",
            AsmOp::U64Mul => "u64_mul",
            AsmOp::ISizeDiv => "int_div",
            AsmOp::I8Div => "i8_div",
            AsmOp::I16Div => "i16_div",
            AsmOp::I32Div => "i32_div",
            AsmOp::I64Div => "i64_div",
            AsmOp::USizeDiv => "uint_div",
            AsmOp::U8Div => "u8_div",
            AsmOp::U16Div => "u16_div",
            AsmOp::U32Div => "u32_div",
            AsmOp::U64Div => "u64_div",
            AsmOp::ISizeMod => "int_mod",
            AsmOp::I8Mod => "i8_mod",
            AsmOp::I16Mod => "i16_mod",
            AsmOp::I32Mod => "i32_mod",
            AsmOp::I64Mod => "i64_mod",
            AsmOp::USizeMod => "uint_mod",
            AsmOp::U8Mod => "u8_mod",
            AsmOp::U16Mod => "u16_mod",
            AsmOp::U32Mod => "u32_mod",
            AsmOp::U64Mod => "u64_mod",
            AsmOp::ISizeAnd => "int_and",
            AsmOp::I8And => "i8_and",
            AsmOp::I16And => "i16_and",
            AsmOp::I32And => "i32_and",
            AsmOp::I64And => "i64_and",
            AsmOp::USizeAnd => "uint_and",
            AsmOp::U8And => "u8_and",
            AsmOp::U16And => "u16_and",
            AsmOp::U32And => "u32_and",
            AsmOp::U64And => "u64_and",
            AsmOp::ISizeOr => "int_or",
            AsmOp::I8Or => "i8_or",
            AsmOp::I16Or => "i16_or",
            AsmOp::I32Or => "i32_or",
            AsmOp::I64Or => "i64_or",
            AsmOp::USizeOr => "uint_or",
            AsmOp::U8Or => "u8_or",
            AsmOp::U16Or => "u16_or",
            AsmOp::U32Or => "u32_or",
            AsmOp::U64Or => "u64_or",
            AsmOp::ISizeXor => "int_xor",
            AsmOp::I8Xor => "i8_xor",
            AsmOp::I16Xor => "i16_xor",
            AsmOp::I32Xor => "i32_xor",
            AsmOp::I64Xor => "i64_xor",
            AsmOp::USizeXor => "uint_xor",
            AsmOp::U8Xor => "u8_xor",
            AsmOp::U16Xor => "u16_xor",
            AsmOp::U32Xor => "u32_xor",
            AsmOp::U64Xor => "u64_xor",
            AsmOp::ISizeLt => "int_lt",
            AsmOp::I8Lt => "i8_lt",
            AsmOp::I16Lt => "i16_lt",
            AsmOp::I32Lt => "i32_lt",
            AsmOp::I64Lt => "i64_lt",
            AsmOp::USizeLt => "uint_lt",
            AsmOp::U8Lt => "u8_lt",
            AsmOp::U16Lt => "u16_lt",
            AsmOp::U32Lt => "u32_lt",
            AsmOp::U64Lt => "u64_lt",
            AsmOp::ISizeGt => "int_gt",
            AsmOp::I8Gt => "i8_gt",
            AsmOp::I16Gt => "i16_gt",
            AsmOp::I32Gt => "i32_gt",
            AsmOp::I64Gt => "i64_gt",
            AsmOp::USizeGt => "uint_gt",
            AsmOp::U8Gt => "u8_gt",
            AsmOp::U16Gt => "u16_gt",
            AsmOp::U32Gt => "u32_gt",
            AsmOp::U64Gt => "u64_gt",
            AsmOp::ISizeLtEq => "int_lteq",
            AsmOp::I8LtEq => "i8_lteq",
            AsmOp::I16LtEq => "i16_lteq",
            AsmOp::I32LtEq => "i32_lteq",
            AsmOp::I64LtEq => "i64_lteq",
            AsmOp::USizeLtEq => "uint_lteq",
            AsmOp::U8LtEq => "u8_lteq",
            AsmOp::U16LtEq => "u16_lteq",
            AsmOp::U32LtEq => "u32_lteq",
            AsmOp::U64LtEq => "u64_lteq",
            AsmOp::ISizeGtEq => "int_gteq",
            AsmOp::I8GtEq => "i8_gteq",
            AsmOp::I16GtEq => "i16_gteq",
            AsmOp::I32GtEq => "i32_gteq",
            AsmOp::I64GtEq => "i64_gteq",
            AsmOp::USizeGtEq => "uint_gteq",
            AsmOp::U8GtEq => "u8_gteq",
            AsmOp::U16GtEq => "u16_gteq",
            AsmOp::U32GtEq => "u32_gteq",
            AsmOp::U64GtEq => "u64_gteq",
            AsmOp::ISizeShl => "int_shl",
            AsmOp::I8Shl => "i8_shl",
            AsmOp::I16Shl => "i16_shl",
            AsmOp::I32Shl => "i32_shl",
            AsmOp::I64Shl => "i64_shl",
            AsmOp::USizeShl => "uint_shl",
            AsmOp::U8Shl => "u8_shl",
            AsmOp::U16Shl => "u16_shl",
            AsmOp::U32Shl => "u32_shl",
            AsmOp::U64Shl => "u64_shl",
            AsmOp::ISizeShr => "int_shr",
            AsmOp::I8Shr => "i8_shr",
            AsmOp::I16Shr => "i16_shr",
            AsmOp::I32Shr => "i32_shr",
            AsmOp::I64Shr => "i64_shr",
            AsmOp::USizeShr => "uint_shr",
            AsmOp::U8Shr => "u8_shr",
            AsmOp::U16Shr => "u16_shr",
            AsmOp::U32Shr => "u32_shr",
            AsmOp::U64Shr => "u64_shr",
            AsmOp::ISizeRotl => "int_rotl",
            AsmOp::I8Rotl => "i8_rotl",
            AsmOp::I16Rotl => "i16_rotl",
            AsmOp::I32Rotl => "i32_rotl",
            AsmOp::I64Rotl => "i64_rotl",
            AsmOp::USizeRotl => "uint_rotl",
            AsmOp::U8Rotl => "u8_rotl",
            AsmOp::U16Rotl => "u16_rotl",
            AsmOp::U32Rotl => "u32_rotl",
            AsmOp::U64Rotl => "u64_rotl",
            AsmOp::ISizeRotr => "int_rotr",
            AsmOp::I8Rotr => "i8_rotr",
            AsmOp::I16Rotr => "i16_rotr",
            AsmOp::I32Rotr => "i32_rotr",
            AsmOp::I64Rotr => "i64_rotr",
            AsmOp::USizeRotr => "uint_rotr",
            AsmOp::U8Rotr => "u8_rotr",
            AsmOp::U16Rotr => "u16_rotr",
            AsmOp::U32Rotr => "u32_rotr",
            AsmOp::U64Rotr => "u64_rotr",
        })
    }
}

impl AsmOp {
    pub fn ret_ty(&self) -> Ty {
        match self {
            AsmOp::ISizeEq
            | AsmOp::I8Eq
            | AsmOp::I16Eq
            | AsmOp::I32Eq
            | AsmOp::I64Eq
            | AsmOp::USizeEq
            | AsmOp::U8Eq
            | AsmOp::U16Eq
            | AsmOp::U32Eq
            | AsmOp::U64Eq
            | AsmOp::ISizeNeq
            | AsmOp::I8Neq
            | AsmOp::I16Neq
            | AsmOp::I32Neq
            | AsmOp::I64Neq
            | AsmOp::USizeNeq
            | AsmOp::U8Neq
            | AsmOp::U16Neq
            | AsmOp::U32Neq
            | AsmOp::U64Neq
            | AsmOp::ISizeLt
            | AsmOp::I8Lt
            | AsmOp::I16Lt
            | AsmOp::I32Lt
            | AsmOp::I64Lt
            | AsmOp::USizeLt
            | AsmOp::U8Lt
            | AsmOp::U16Lt
            | AsmOp::U32Lt
            | AsmOp::U64Lt
            | AsmOp::ISizeGt
            | AsmOp::I8Gt
            | AsmOp::I16Gt
            | AsmOp::I32Gt
            | AsmOp::I64Gt
            | AsmOp::USizeGt
            | AsmOp::U8Gt
            | AsmOp::U16Gt
            | AsmOp::U32Gt
            | AsmOp::U64Gt
            | AsmOp::ISizeLtEq
            | AsmOp::I8LtEq
            | AsmOp::I16LtEq
            | AsmOp::I32LtEq
            | AsmOp::I64LtEq
            | AsmOp::USizeLtEq
            | AsmOp::U8LtEq
            | AsmOp::U16LtEq
            | AsmOp::U32LtEq
            | AsmOp::U64LtEq
            | AsmOp::ISizeGtEq
            | AsmOp::I8GtEq
            | AsmOp::I16GtEq
            | AsmOp::I32GtEq
            | AsmOp::I64GtEq
            | AsmOp::USizeGtEq
            | AsmOp::U8GtEq
            | AsmOp::U16GtEq
            | AsmOp::U32GtEq
            | AsmOp::U64GtEq => Ty::bool(),
            AsmOp::ISizeAdd
            | AsmOp::ISizeSub
            | AsmOp::ISizeMul
            | AsmOp::ISizeDiv
            | AsmOp::ISizeMod
            | AsmOp::ISizeAnd
            | AsmOp::ISizeOr
            | AsmOp::ISizeXor
            | AsmOp::ISizeShl
            | AsmOp::ISizeShr
            | AsmOp::ISizeRotl
            | AsmOp::ISizeRotr => Ty::int(),
            AsmOp::I8Add
            | AsmOp::I8Sub
            | AsmOp::I8Mul
            | AsmOp::I8Div
            | AsmOp::I8Mod
            | AsmOp::I8And
            | AsmOp::I8Or
            | AsmOp::I8Xor
            | AsmOp::I8Shl
            | AsmOp::I8Shr
            | AsmOp::I8Rotl
            | AsmOp::I8Rotr => Ty::i8(),
            AsmOp::I16Add
            | AsmOp::I16Sub
            | AsmOp::I16Mul
            | AsmOp::I16Div
            | AsmOp::I16Mod
            | AsmOp::I16And
            | AsmOp::I16Or
            | AsmOp::I16Xor
            | AsmOp::I16Shl
            | AsmOp::I16Shr
            | AsmOp::I16Rotl
            | AsmOp::I16Rotr => Ty::i16(),
            AsmOp::I32Add
            | AsmOp::I32Sub
            | AsmOp::I32Mul
            | AsmOp::I32Div
            | AsmOp::I32Mod
            | AsmOp::I32And
            | AsmOp::I32Or
            | AsmOp::I32Xor
            | AsmOp::I32Shl
            | AsmOp::I32Shr
            | AsmOp::I32Rotl
            | AsmOp::I32Rotr => Ty::i32(),
            AsmOp::I64Add
            | AsmOp::I64Sub
            | AsmOp::I64Mul
            | AsmOp::I64Div
            | AsmOp::I64Mod
            | AsmOp::I64And
            | AsmOp::I64Or
            | AsmOp::I64Xor
            | AsmOp::I64Shl
            | AsmOp::I64Shr
            | AsmOp::I64Rotl
            | AsmOp::I64Rotr => Ty::i64(),
            AsmOp::USizeAdd
            | AsmOp::USizeSub
            | AsmOp::USizeMul
            | AsmOp::USizeDiv
            | AsmOp::USizeMod
            | AsmOp::USizeAnd
            | AsmOp::USizeOr
            | AsmOp::USizeXor
            | AsmOp::USizeShl
            | AsmOp::USizeShr
            | AsmOp::USizeRotl
            | AsmOp::USizeRotr => Ty::uint(),
            AsmOp::U8Add
            | AsmOp::U8Sub
            | AsmOp::U8Mul
            | AsmOp::U8Div
            | AsmOp::U8Mod
            | AsmOp::U8And
            | AsmOp::U8Or
            | AsmOp::U8Xor
            | AsmOp::U8Shl
            | AsmOp::U8Shr
            | AsmOp::U8Rotl
            | AsmOp::U8Rotr => Ty::u8(),
            AsmOp::U16Add
            | AsmOp::U16Sub
            | AsmOp::U16Mul
            | AsmOp::U16Div
            | AsmOp::U16Mod
            | AsmOp::U16And
            | AsmOp::U16Or
            | AsmOp::U16Xor
            | AsmOp::U16Shl
            | AsmOp::U16Shr
            | AsmOp::U16Rotl
            | AsmOp::U16Rotr => Ty::u16(),
            AsmOp::U32Add
            | AsmOp::U32Sub
            | AsmOp::U32Mul
            | AsmOp::U32Div
            | AsmOp::U32Mod
            | AsmOp::U32And
            | AsmOp::U32Or
            | AsmOp::U32Xor
            | AsmOp::U32Shl
            | AsmOp::U32Shr
            | AsmOp::U32Rotl
            | AsmOp::U32Rotr => Ty::u32(),
            AsmOp::U64Add
            | AsmOp::U64Sub
            | AsmOp::U64Mul
            | AsmOp::U64Div
            | AsmOp::U64Mod
            | AsmOp::U64And
            | AsmOp::U64Or
            | AsmOp::U64Xor
            | AsmOp::U64Shl
            | AsmOp::U64Shr
            | AsmOp::U64Rotl
            | AsmOp::U64Rotr => Ty::u64(),
            AsmOp::Malloc => Ty::ptr(Ty::Var(TyVar(Path::from("'a")))),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AsmOperand {
    Var(String),
    Int(u64),
}

impl std::fmt::Display for AsmOperand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AsmOperand::Var(s) => write!(f, "{}", s),
            AsmOperand::Int(i) => write!(f, "{}", i),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Asm {
    pub ret_ty: Option<Parsed<Ty>>,
    pub inst: Vec<(AsmOp, Vec<AsmOperand>)>,
}

impl std::fmt::Display for Asm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "asm{} {{\n{}\n}}",
            if let Some(ret_ty) = &self.ret_ty {
                format!("({})", ret_ty)
            } else {
                str!("")
            },
            indent(
                map_join(&self.inst, "\n", |(x, y)| {
                    format!("{} {}", x, join(y, " "))
                }),
                2
            )
        )
    }
}

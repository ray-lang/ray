//! Semantic token support for `ray-lsp`.

use ray::ide::semantic_tokens::{
    self as semantic, SemanticToken as RayToken, SemanticTokenKind as RayKind,
    SemanticTokenModifier as RayModifier,
};
use tower_lsp::lsp_types::{
    SemanticToken, SemanticTokenModifier, SemanticTokenType, SemanticTokens, SemanticTokensLegend,
};

const TOKEN_TYPES: [SemanticTokenType; 10] = [
    SemanticTokenType::KEYWORD,
    SemanticTokenType::FUNCTION,
    SemanticTokenType::VARIABLE,
    SemanticTokenType::TYPE,
    SemanticTokenType::PARAMETER,
    SemanticTokenType::PROPERTY,
    SemanticTokenType::STRING,
    SemanticTokenType::OPERATOR,
    SemanticTokenType::NAMESPACE,
    SemanticTokenType::COMMENT,
];

const TOKEN_TYPE_KEYWORD: usize = 0;
const TOKEN_TYPE_FUNCTION: usize = 1;
const TOKEN_TYPE_VARIABLE: usize = 2;
const TOKEN_TYPE_TYPE: usize = 3;
const TOKEN_TYPE_PARAMETER: usize = 4;
const TOKEN_TYPE_FIELD: usize = 5;
const TOKEN_TYPE_LITERAL: usize = 6;
const TOKEN_TYPE_OPERATOR: usize = 7;
const TOKEN_TYPE_NAMESPACE: usize = 8;
const TOKEN_TYPE_COMMENT: usize = 9;

const TOKEN_MODIFIERS: [SemanticTokenModifier; 3] = [
    SemanticTokenModifier::DECLARATION,
    SemanticTokenModifier::DEFINITION,
    SemanticTokenModifier::MODIFICATION,
];

const MOD_DECLARATION: usize = 0;
const MOD_DEFINITION: usize = 1;
const MOD_MUTABLE: usize = 2;

/// Semantic token legend advertised to clients.
pub fn legend() -> SemanticTokensLegend {
    SemanticTokensLegend {
        token_types: TOKEN_TYPES.iter().cloned().collect(),
        token_modifiers: TOKEN_MODIFIERS.iter().cloned().collect(),
    }
}

/// Produces semantic tokens for the provided Ray source.
pub fn semantic_tokens(source: &str) -> SemanticTokens {
    let tokens = semantic::collect_from_source(source);
    encode_tokens(&tokens, source)
}

fn encode_tokens(tokens: &[RayToken], source: &str) -> SemanticTokens {
    let line_starts = compute_line_starts(source);
    let mut data: Vec<SemanticToken> = Vec::new();
    let mut prev_line: u32 = 0;
    let mut prev_col: u32 = 0;
    let mut first = true;

    for token in tokens {
        let start_offset = token.span.start.offset.min(source.len());
        let mut end_offset = token.span.end.offset.min(source.len());

        if start_offset >= end_offset {
            continue;
        }

        let (start_line, start_col) = offset_to_position(start_offset, &line_starts, source);
        let end_position_offset = end_offset.saturating_sub(1);
        let (end_line, _) = offset_to_position(end_position_offset, &line_starts, source);

        if end_line > start_line {
            let next_start = line_starts
                .get(start_line as usize + 1)
                .copied()
                .unwrap_or(source.len());
            let trimmed = next_start.saturating_sub(1);
            end_offset = if trimmed > start_offset {
                trimmed
            } else {
                next_start
            };
        }

        if end_offset <= start_offset {
            continue;
        }

        let token_slice = &source[start_offset..end_offset];
        let length = utf16_len(token_slice);
        if length == 0 {
            continue;
        }

        let delta_line = if first {
            start_line
        } else {
            start_line.saturating_sub(prev_line)
        };

        let delta_start = if first {
            start_col
        } else if delta_line == 0 {
            start_col.saturating_sub(prev_col)
        } else {
            start_col
        };

        let token_type = kind_to_index(token.kind) as u32;
        let modifiers = modifiers_bitset(&token.modifiers);

        data.push(SemanticToken {
            delta_line,
            delta_start,
            length,
            token_type,
            token_modifiers_bitset: modifiers,
        });

        prev_line = start_line;
        prev_col = start_col;
        first = false;
    }

    SemanticTokens {
        result_id: None,
        data,
    }
}

fn kind_to_index(kind: RayKind) -> usize {
    match kind {
        RayKind::Keyword => TOKEN_TYPE_KEYWORD,
        RayKind::Function => TOKEN_TYPE_FUNCTION,
        RayKind::Variable => TOKEN_TYPE_VARIABLE,
        RayKind::Type | RayKind::Trait => TOKEN_TYPE_TYPE,
        RayKind::Parameter => TOKEN_TYPE_PARAMETER,
        RayKind::Field => TOKEN_TYPE_FIELD,
        RayKind::Literal => TOKEN_TYPE_LITERAL,
        RayKind::Operator => TOKEN_TYPE_OPERATOR,
        RayKind::Namespace => TOKEN_TYPE_NAMESPACE,
        RayKind::Comment => TOKEN_TYPE_COMMENT,
    }
}

fn modifiers_bitset(modifiers: &[RayModifier]) -> u32 {
    let mut bitset = 0u32;
    for modifier in modifiers {
        let index = match modifier {
            RayModifier::Declaration => MOD_DECLARATION,
            RayModifier::Definition => MOD_DEFINITION,
            RayModifier::Mutable => MOD_MUTABLE,
        };
        bitset |= 1 << index;
    }
    bitset
}

fn compute_line_starts(text: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (idx, ch) in text.char_indices() {
        if ch == '\n' {
            starts.push(idx + ch.len_utf8());
        }
    }
    if starts.last().copied().unwrap_or(0) != text.len() {
        starts.push(text.len());
    }
    if starts.len() == 1 {
        starts.push(text.len());
    }
    starts
}

fn offset_to_position(offset: usize, line_starts: &[usize], text: &str) -> (u32, u32) {
    if line_starts.len() < 2 {
        return (0, 0);
    }

    let clamped = offset.min(text.len());
    let line_idx = match line_starts.binary_search(&clamped) {
        Ok(idx) => {
            if idx == line_starts.len() - 1 {
                idx.saturating_sub(1)
            } else {
                idx
            }
        }
        Err(0) => 0,
        Err(idx) => idx - 1,
    };

    let line_start = line_starts[line_idx];
    let line_end = line_starts.get(line_idx + 1).copied().unwrap_or(text.len());
    let clamped_end = clamped.min(line_end);

    let column_slice = &text[line_start..clamped_end];
    let column = utf16_len(column_slice);

    (line_idx as u32, column)
}

fn utf16_len(text: &str) -> u32 {
    text.chars().map(|c| c.len_utf16() as u32).sum()
}

pub fn pretty_dump(data: &[SemanticToken], source: &str, legend: &SemanticTokensLegend) -> String {
    // Split text into lines for previewing token slices
    let lines: Vec<&str> = source.split_inclusive('\n').collect();

    let mut out = String::new();
    let mut abs_line: u32 = 0;
    let mut abs_col: u32 = 0;

    for tok in data {
        abs_line += tok.delta_line;
        abs_col = if tok.delta_line == 0 {
            abs_col + tok.delta_start
        } else {
            tok.delta_start
        };

        let type_name = legend
            .token_types
            .get(tok.token_type as usize)
            .map(|t| t.as_str())
            .unwrap_or("unknown");

        // Decode modifier bitset using legend ordering
        let mut mods: Vec<&str> = Vec::new();
        for (bit, m) in legend.token_modifiers.iter().enumerate() {
            if (tok.token_modifiers_bitset & (1 << bit)) != 0 {
                mods.push(m.as_str());
            }
        }
        let mods_joined = if mods.is_empty() {
            "-".to_string()
        } else {
            mods.join(",")
        };

        let line_txt = lines.get(abs_line as usize).copied().unwrap_or_default();
        let start = abs_col as usize;
        let text = line_txt
            .chars()
            .skip(start)
            .take(tok.length as usize)
            .collect::<String>();

        use std::fmt::Write as _;
        let _ = writeln!(
            &mut out,
            "L{}:{} len={} type={} mods={} text=\"{}\"",
            abs_line, abs_col, tok.length, type_name, mods_joined, text
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn decode_tokens(tokens: &SemanticTokens) -> Vec<(u32, u32, u32, u32)> {
        let mut line = 0u32;
        let mut col = 0u32;
        tokens
            .data
            .iter()
            .map(|token| {
                line += token.delta_line;
                if token.delta_line == 0 {
                    col += token.delta_start;
                } else {
                    col = token.delta_start;
                }
                (line, col, token.length, token.token_type)
            })
            .collect()
    }

    #[test]
    fn collects_semantic_tokens_for_basic_constructs() {
        let source = r#"
// example comment
struct Foo {
    value: int
}

fn make(value: int) -> Foo {
    Foo { value } // trailing comment
}
"#;

        let tokens = semantic_tokens(source);
        assert!(!tokens.data.is_empty());

        let decoded = decode_tokens(&tokens);
        assert!(
            decoded.iter().any(|(line, col, len, ty)| {
                *ty == TOKEN_TYPE_FUNCTION as u32 && *line == 6 && *col == 3 && *len == 4
            }),
            "expected function name token at line 6 col 3 with length 4, got {decoded:?}"
        );
        assert!(
            decoded
                .iter()
                .any(|(_, _, _, ty)| *ty == TOKEN_TYPE_KEYWORD as u32),
            "expected at least one keyword token"
        );
        assert!(
            decoded
                .iter()
                .any(|(_, _, _, ty)| *ty == TOKEN_TYPE_COMMENT as u32),
            "expected at least one comment token"
        );
        assert!(
            decoded.iter().any(|(line, _, _, ty)| {
                *ty == TOKEN_TYPE_COMMENT as u32 && *line == 6
            }),
            "expected trailing comment token on function body line, got {decoded:?}"
        );

        assert!(
            decoded
                .iter()
                .any(|(_, _, _, ty)| *ty == TOKEN_TYPE_TYPE as u32),
            "expected at least one type token"
        );
        assert!(
            decoded
                .iter()
                .any(|(_, _, _, ty)| *ty == TOKEN_TYPE_FUNCTION as u32),
            "expected at least one function token"
        );
        assert!(
            decoded
                .iter()
                .any(|(_, _, _, ty)| *ty == TOKEN_TYPE_PARAMETER as u32),
            "expected at least one parameter token"
        );
        assert!(
            decoded
                .iter()
                .any(|(_, _, _, ty)| *ty == TOKEN_TYPE_FIELD as u32),
            "expected at least one field token"
        );
    }

    #[test]
    fn produces_tokens_for_core_library() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("crate directory")
            .join("..")
            .join("lib/core/core.ray");
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
        let tokens = semantic_tokens(&source);
        assert!(
            !tokens.data.is_empty(),
            "expected semantic tokens for {}, got empty result",
            path.display()
        );
    }

    #[test]
    fn classifies_types_functions_and_parameters() {
        let source = r#"
// example comment
struct Foo {
    value: int
}

fn make(value: int) -> Foo {
    Foo { value } // trailing comment
}
"#;
        let tokens = semantic_tokens(source);
        let mut saw_type = false;
        let mut saw_function = false;
        let mut saw_parameter = false;
        let mut saw_field = false;
        let mut saw_keyword = false;
        let mut saw_comment = false;

        for token in &tokens.data {
            match token.token_type {
                x if x == TOKEN_TYPE_TYPE as u32 => saw_type = true,
                x if x == TOKEN_TYPE_FUNCTION as u32 => saw_function = true,
                x if x == TOKEN_TYPE_PARAMETER as u32 => saw_parameter = true,
                x if x == TOKEN_TYPE_FIELD as u32 => saw_field = true,
                x if x == TOKEN_TYPE_KEYWORD as u32 => saw_keyword = true,
                x if x == TOKEN_TYPE_COMMENT as u32 => saw_comment = true,
                _ => {}
            }
        }

        assert!(saw_type, "expected at least one type token");
        assert!(saw_function, "expected at least one function token");
        assert!(saw_parameter, "expected at least one parameter token");
        assert!(saw_field, "expected at least one field token");
        assert!(saw_keyword, "expected at least one keyword token");
        assert!(saw_comment, "expected at least one comment token");
    }
}

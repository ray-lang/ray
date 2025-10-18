//! Helpers for gathering lexer output that will back semantic token support.

use ray::{
    ast::token::TokenKind,
    parse::lexer::{lexemes, Lexeme, Preceding},
};
use tower_lsp::lsp_types::{
    SemanticToken, SemanticTokenType, SemanticTokens, SemanticTokensLegend,
};

const TOKEN_TYPES: [SemanticTokenType; 9] = [
    SemanticTokenType::KEYWORD,
    SemanticTokenType::FUNCTION,
    SemanticTokenType::VARIABLE,
    SemanticTokenType::TYPE,
    SemanticTokenType::PARAMETER,
    SemanticTokenType::NUMBER,
    SemanticTokenType::COMMENT,
    SemanticTokenType::OPERATOR,
    SemanticTokenType::STRING,
];

const TOKEN_TYPE_KEYWORD: usize = 0;
const TOKEN_TYPE_FUNCTION: usize = 1;
const TOKEN_TYPE_VARIABLE: usize = 2;
const TOKEN_TYPE_TYPE: usize = 3;
const TOKEN_TYPE_PARAMETER: usize = 4;
const TOKEN_TYPE_NUMBER: usize = 5;
const TOKEN_TYPE_COMMENT: usize = 6;
const TOKEN_TYPE_OPERATOR: usize = 7;
const TOKEN_TYPE_STRING: usize = 8;

#[derive(Clone, Copy)]
enum TokenCategory {
    Keyword,
    Function,
    Variable,
    Type,
    Parameter,
    Number,
    Comment,
    Operator,
    String,
}

impl TokenCategory {
    fn as_index(self) -> usize {
        match self {
            TokenCategory::Keyword => TOKEN_TYPE_KEYWORD,
            TokenCategory::Function => TOKEN_TYPE_FUNCTION,
            TokenCategory::Variable => TOKEN_TYPE_VARIABLE,
            TokenCategory::Type => TOKEN_TYPE_TYPE,
            TokenCategory::Parameter => TOKEN_TYPE_PARAMETER,
            TokenCategory::Number => TOKEN_TYPE_NUMBER,
            TokenCategory::Comment => TOKEN_TYPE_COMMENT,
            TokenCategory::Operator => TOKEN_TYPE_OPERATOR,
            TokenCategory::String => TOKEN_TYPE_STRING,
        }
    }
}

/// Semantic token legend advertised to clients.
pub fn legend() -> SemanticTokensLegend {
    SemanticTokensLegend {
        token_types: TOKEN_TYPES.iter().cloned().collect(),
        token_modifiers: vec![],
    }
}

/// Produces semantic tokens for the provided Ray source.
pub fn semantic_tokens(source: &str) -> SemanticTokens {
    let lexemes = lexemes(source);
    encode_tokens(&lexemes, source)
}

fn encode_tokens(lexemes: &[Lexeme], source: &str) -> SemanticTokens {
    let mut data: Vec<SemanticToken> = Vec::new();
    let mut prev_line: u32 = 0;
    let mut prev_col: u32 = 0;
    let mut first = true;
    let mut string_state: Option<char> = None;

    let mut push_token = |span: ray::span::Span, category: TokenCategory| {
        if span.start.offset >= source.len() || span.start.offset > span.end.offset {
            return;
        }

        let slice_end = span.end.offset.min(source.len());
        if slice_end <= span.start.offset {
            return;
        }

        let mut token_text = &source[span.start.offset..slice_end];
        if let Some(pos) = token_text.find('\n') {
            token_text = &token_text[..pos];
        }

        if token_text.is_empty() {
            return;
        }

        let length = token_text.chars().count() as u32;
        if length == 0 {
            return;
        }

        let start_line = span.start.lineno as u32;
        let start_col = span.start.col as u32;

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

        data.push(SemanticToken {
            delta_line,
            delta_start,
            length,
            token_type: category.as_index() as u32,
            token_modifiers_bitset: 0,
        });

        prev_line = start_line;
        prev_col = start_col;
        first = false;
    };

    for (index, lex) in lexemes.iter().enumerate() {
        for trivia in &lex.leading {
            if let Preceding::Comment(token) = trivia {
                push_token(token.span, TokenCategory::Comment);
            }
        }

        let kind = &lex.token.kind;
        let span = lex.token.span;

        if matches!(kind, TokenKind::Whitespace | TokenKind::NewLine) {
            continue;
        }

        if let Some(delim) = string_state {
            push_token(span, TokenCategory::String);
            if (matches!(kind, TokenKind::DoubleQuote) && delim == '"')
                || (matches!(kind, TokenKind::SingleQuote) && delim == '\'')
            {
                string_state = None;
            }
            continue;
        }

        match kind {
            TokenKind::Default | TokenKind::New => {
                let category = if is_function_position(lexemes, index) {
                    TokenCategory::Function
                } else {
                    TokenCategory::Keyword
                };
                push_token(span, category);
                continue;
            }
            TokenKind::DoubleQuote => {
                push_token(span, TokenCategory::String);
                string_state = Some('"');
                continue;
            }
            TokenKind::SingleQuote => {
                push_token(span, TokenCategory::String);
                string_state = Some('\'');
                continue;
            }
            TokenKind::Comment { .. } => {
                push_token(span, TokenCategory::Comment);
                continue;
            }
            TokenKind::Integer { .. } | TokenKind::Float { .. } => {
                push_token(span, TokenCategory::Number);
                continue;
            }
            TokenKind::Bool(_) | TokenKind::Nil => {
                push_token(span, TokenCategory::Keyword);
                continue;
            }
            TokenKind::UnicodeEscSeq(_) => {
                push_token(span, TokenCategory::String);
                continue;
            }
            TokenKind::Modifier(_) => {
                push_token(span, TokenCategory::Keyword);
                continue;
            }
            TokenKind::PrefixedIdent(prefix, ident) => {
                let category = classify_identifier(ident, Some(*prefix), lexemes, index);
                push_token(span, category);
                continue;
            }
            TokenKind::Identifier(ident) => {
                let category = classify_identifier(ident, None, lexemes, index);
                push_token(span, category);
                continue;
            }
            TokenKind::Mut
            | TokenKind::Const
            | TokenKind::Fn
            | TokenKind::UpperFn
            | TokenKind::If
            | TokenKind::Unless
            | TokenKind::Else
            | TokenKind::Then
            | TokenKind::Return
            | TokenKind::Break
            | TokenKind::Async
            | TokenKind::Extern
            | TokenKind::Struct
            | TokenKind::Enum
            | TokenKind::Trait
            | TokenKind::Impl
            | TokenKind::Object
            | TokenKind::TypeAlias
            | TokenKind::Import
            | TokenKind::With
            | TokenKind::As
            | TokenKind::For
            | TokenKind::While
            | TokenKind::Loop
            | TokenKind::In
            | TokenKind::Is
            | TokenKind::Where
            | TokenKind::Asm => {
                push_token(span, TokenCategory::Keyword);
                continue;
            }
            TokenKind::Equals
            | TokenKind::Gt
            | TokenKind::Lt
            | TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Asterisk
            | TokenKind::Slash
            | TokenKind::Percent
            | TokenKind::Ampersand
            | TokenKind::Pipe
            | TokenKind::Exclamation
            | TokenKind::Caret
            | TokenKind::Tilde
            | TokenKind::LeftParen
            | TokenKind::RightParen
            | TokenKind::LeftCurly
            | TokenKind::RightCurly
            | TokenKind::LeftBracket
            | TokenKind::RightBracket
            | TokenKind::Question
            | TokenKind::Dot
            | TokenKind::RangeInclusive
            | TokenKind::RangeExclusive
            | TokenKind::Ellipsis
            | TokenKind::Comma
            | TokenKind::Semi
            | TokenKind::Colon
            | TokenKind::DoubleColon
            | TokenKind::Arrow
            | TokenKind::FatArrow
            | TokenKind::At
            | TokenKind::Dollar
            | TokenKind::Underscore
            | TokenKind::Hash => {
                push_token(span, TokenCategory::Operator);
                continue;
            }
            TokenKind::Illegal(_) | TokenKind::EOF => {}
            _ => {}
        }
    }

    SemanticTokens {
        result_id: None,
        data,
    }
}

fn classify_identifier(
    name: &str,
    prefix: Option<char>,
    lexemes: &[Lexeme],
    index: usize,
) -> TokenCategory {
    if name == "self" {
        return TokenCategory::Parameter;
    }
    if name == "Self" {
        return TokenCategory::Type;
    }

    if matches!(prefix, Some('\'')) {
        return TokenCategory::Parameter;
    }

    if matches!(name, "let") {
        return TokenCategory::Keyword;
    }

    let previous = previous_non_trivia(lexemes, index);
    if matches!(
        previous,
        Some(
            TokenKind::Struct
                | TokenKind::Enum
                | TokenKind::Trait
                | TokenKind::TypeAlias
                | TokenKind::Impl
                | TokenKind::Object
        )
    ) {
        return TokenCategory::Type;
    }

    if is_function_position(lexemes, index) {
        return TokenCategory::Function;
    }

    if is_type_like(name, prefix) {
        return TokenCategory::Type;
    }

    TokenCategory::Variable
}

fn is_function_position(lexemes: &[Lexeme], index: usize) -> bool {
    if matches!(
        previous_non_trivia(lexemes, index),
        Some(TokenKind::Fn | TokenKind::UpperFn)
    ) {
        return true;
    }

    matches!(next_non_trivia(lexemes, index), Some(TokenKind::LeftParen))
}

fn is_type_like(name: &str, prefix: Option<char>) -> bool {
    if matches!(prefix, Some('#')) {
        return false;
    }
    name.chars()
        .next()
        .map(|c| c.is_ascii_uppercase() || c == '_')
        .unwrap_or(false)
}

fn previous_non_trivia<'a>(lexemes: &'a [Lexeme], index: usize) -> Option<&'a TokenKind> {
    let mut current = index as isize - 1;
    while current >= 0 {
        let kind = &lexemes[current as usize].token.kind;
        if !is_trivia(kind) {
            return Some(kind);
        }
        current -= 1;
    }
    None
}

fn next_non_trivia<'a>(lexemes: &'a [Lexeme], index: usize) -> Option<&'a TokenKind> {
    let mut current = index + 1;
    while current < lexemes.len() {
        let kind = &lexemes[current].token.kind;
        if !is_trivia(kind) {
            return Some(kind);
        }
        current += 1;
    }
    None
}

fn is_trivia(kind: &TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Whitespace | TokenKind::NewLine | TokenKind::Comment { .. }
    )
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
    fn classify_module_and_function_docs() {
        let source = "//! module docs\n/// fn docs\nfn main() {\n    mut x = 1\n    x = 2\n}\n";
        let tokens = semantic_tokens(source);
        assert!(!tokens.data.is_empty());

        let decoded = decode_tokens(&tokens);
        // Expect the first token (module doc) to be classified as comment.
        assert_eq!(decoded[0].0, 0); // line
        assert_eq!(decoded[0].3, TOKEN_TYPE_COMMENT as u32);

        // Ensure we emit a keyword for `fn`.
        let fn_token = decoded
            .iter()
            .find(|(_, _, _, ty)| *ty == TOKEN_TYPE_KEYWORD as u32)
            .expect("expected keyword token");
        assert_eq!(fn_token.0, 2);
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
struct Foo {
    fn new(self) -> Foo {
        Foo::default()
    }
}

let value = Foo::new();
let text = "hello";
"#;
        let tokens = semantic_tokens(source);

        let mut saw_type = false;
        let mut saw_function = false;
        let mut saw_parameter = false;
        let mut saw_string = false;

        for token in &tokens.data {
            match token.token_type {
                x if x == TOKEN_TYPE_TYPE as u32 => saw_type = true,
                x if x == TOKEN_TYPE_FUNCTION as u32 => saw_function = true,
                x if x == TOKEN_TYPE_PARAMETER as u32 => saw_parameter = true,
                x if x == TOKEN_TYPE_STRING as u32 => saw_string = true,
                _ => {}
            }
        }

        assert!(saw_type, "expected at least one type token");
        assert!(saw_function, "expected at least one function token");
        assert!(saw_parameter, "expected at least one parameter token");
        assert!(saw_string, "expected at least one string token");
    }
}

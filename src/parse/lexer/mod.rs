use crate::{
    ast::{
        Modifier,
        token::{CommentKind, IntegerBase, Token, TokenKind},
    },
    span::{Pos, Span},
};

use std::collections::VecDeque;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Preceding {
    Whitespace(Token),
    Comment(Token),
}

/// A single lexeme produced by the Ray lexer along with any leading trivia.
#[derive(Clone, Debug)]
pub struct Lexeme {
    pub leading: Vec<Preceding>,
    pub token: Token,
}

pub struct Lexer {
    src: Vec<char>,
    curr_pos: Pos,
    stash_pos: Pos,
    last_tok_span: Span,
    token_stash: VecDeque<Token>,
    stash: VecDeque<(Vec<Preceding>, Token)>,
}

fn is_tok_comment(tok: &Token) -> bool {
    matches!(tok.kind, TokenKind::Comment { .. })
}

fn is_tok_whitespace(tok: &Token) -> bool {
    matches!(tok.kind, TokenKind::Whitespace | TokenKind::NewLine)
}

fn is_valid_id_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

impl Lexer {
    pub fn new(src: &str) -> Lexer {
        Lexer {
            src: src.chars().collect(),
            curr_pos: Pos::empty(),
            stash_pos: Pos::empty(),
            last_tok_span: Span::new(),
            token_stash: VecDeque::new(),
            stash: VecDeque::new(),
        }
    }

    pub fn is_eof(&self) -> bool {
        self.src.get(self.stash_pos.offset).is_none()
    }

    fn eof(&mut self) -> Token {
        Token {
            kind: TokenKind::EOF,
            span: Span::from(self.position()),
        }
    }

    fn char_at(&self, index: usize) -> Option<char> {
        self.src.get(index).map(|c| *c)
    }

    fn next_char(&mut self) -> Option<char> {
        let ch = self.char_at(self.stash_pos.offset)?;
        if ch == '\n' {
            self.stash_pos.lineno += 1;
            self.stash_pos.col = 0;
        } else {
            self.stash_pos.col += 1;
        }
        self.stash_pos.offset += 1;
        Some(ch)
    }

    fn next_char_str(&mut self) -> Option<String> {
        self.next_char().map(|c| c.to_string())
    }

    fn first(&self) -> char {
        self.char_at(self.stash_pos.offset).unwrap_or('\0')
    }

    fn second(&self) -> char {
        self.char_at(self.stash_pos.offset + 1).unwrap_or('\0')
    }

    fn consume_char(&mut self) -> Option<char> {
        let c = self.next_char();
        self.curr_pos = self.stash_pos;
        c
    }

    fn consume_chars(&mut self, n: usize) {
        // consume `n` characters
        for _ in 0..n {
            self.consume_char();
        }
    }

    fn next_char_while(
        &mut self,
        start_ch: Option<char>,
        mut f: impl FnMut(char) -> bool,
    ) -> String {
        let mut s = if let Some(ch) = start_ch {
            ch.to_string()
        } else {
            String::new()
        };
        while f(self.first()) {
            if let Some(ch) = self.next_char() {
                s.push(ch);
            } else {
                break;
            }
        }
        s
    }

    fn ident(&mut self, start_ch: char) -> String {
        self.next_char_while(Some(start_ch), is_valid_id_char)
    }

    fn number(&mut self) -> String {
        self.next_char_while(None, |c| c == '_' || c.is_ascii_digit())
    }

    fn hex(&mut self) -> String {
        self.next_char_while(None, |c| c == '_' || c.is_ascii_hexdigit())
    }

    fn octal(&mut self) -> String {
        self.next_char_while(None, |c| c == '_' || (c >= '0' && c <= '7'))
    }

    fn size_suffix(&mut self) -> String {
        self.next_char_while(None, |c| c.is_ascii_digit())
    }

    fn next_str(&mut self) -> String {
        // build a string leading up to whitespace
        self.next_char_while(None, |c| !c.is_whitespace())
    }

    pub fn quoted_string(&mut self, quote: char) -> (String, bool) {
        // first rewind the lexer, so there's nothing in the stash, so
        // we can get the raw characters back
        self.rewind_tokens();

        let mut s = String::new();
        while let Some(ch) = self.next_char() {
            match ch {
                c if c == quote => {
                    return (s, true);
                }
                '\\' if self.first() == 'n' => {
                    self.next_char().unwrap();
                    s.push('\n');
                }
                '\\' if self.first() == '\\' || self.first() == quote => {
                    s.push(self.next_char().unwrap());
                }
                _ => s.push(ch),
            }
        }
        (s, false)
    }

    fn suffix(&mut self) -> (Option<String>, bool) {
        let mut is_float = false;
        match self.first() {
            'u' | 'i' | 'f' => {
                let k = self.next_char_str().unwrap();
                if k == "f" {
                    is_float = true;
                }
                (Some(k + &self.size_suffix()), is_float)
            }
            _ => (None, false),
        }
    }

    fn keyword_or_ident(&mut self, start_ch: char) -> TokenKind {
        let id = self.ident(start_ch);
        match id.as_str() {
            "mut" => TokenKind::Mut,
            "const" => TokenKind::Const,
            "if" => TokenKind::If,
            "unless" => TokenKind::Unless,
            "else" => TokenKind::Else,
            "then" => TokenKind::Then,
            "Fn" => TokenKind::UpperFn,
            "fn" => TokenKind::Fn,
            "return" => TokenKind::Return,
            "break" => TokenKind::Break,
            "async" => TokenKind::Async,
            "extern" => TokenKind::Extern,
            "struct" => TokenKind::Struct,
            "enum" => TokenKind::Enum,
            "trait" => TokenKind::Trait,
            "default" => TokenKind::Default,
            "impl" => TokenKind::Impl,
            "object" => TokenKind::Object,
            "typealias" => TokenKind::TypeAlias,
            "with" => TokenKind::With,
            "import" => TokenKind::Import,
            "as" => TokenKind::As,
            "for" => TokenKind::For,
            "while" => TokenKind::While,
            "loop" => TokenKind::Loop,
            "in" => TokenKind::In,
            "is" => TokenKind::Is,
            "where" => TokenKind::Where,
            "asm" => TokenKind::Asm,
            "new" => TokenKind::New,
            "pub" => TokenKind::Modifier(Modifier::Pub),
            "static" => TokenKind::Modifier(Modifier::Static),
            "hidden" => TokenKind::Modifier(Modifier::Hidden),
            "internal" => TokenKind::Modifier(Modifier::Internal),
            "unsafe" => TokenKind::Modifier(Modifier::Unsafe),
            "wasi" => TokenKind::Modifier(Modifier::Wasi),
            "nil" => TokenKind::Nil,
            "true" => TokenKind::Bool(true),
            "false" => TokenKind::Bool(false),
            _ => TokenKind::Identifier(id),
        }
    }

    fn next_token(&mut self) -> Token {
        let start = self.stash_pos;
        if !self.is_eof() {
            if let Some(c) = self.next_char() {
                let kind = match c {
                    // newline and whitespace
                    '\n' => TokenKind::NewLine,
                    c if c.is_whitespace() => TokenKind::Whitespace,

                    // single symbol tokens
                    ';' => TokenKind::Semi,
                    '(' => TokenKind::LeftParen,
                    ')' => TokenKind::RightParen,
                    '{' => TokenKind::LeftCurly,
                    '}' => TokenKind::RightCurly,
                    '[' => TokenKind::LeftBracket,
                    ']' => TokenKind::RightBracket,
                    ',' => TokenKind::Comma,
                    '@' => TokenKind::At,
                    '$' => TokenKind::Dollar,
                    '~' => TokenKind::Tilde,
                    '!' => TokenKind::Exclamation,
                    '>' => TokenKind::Gt,
                    '<' => TokenKind::Lt,
                    '+' => TokenKind::Plus,
                    '*' => TokenKind::Asterisk,
                    '%' => TokenKind::Percent,
                    '&' => TokenKind::Ampersand,
                    '|' => TokenKind::Pipe,
                    '^' => TokenKind::Caret,
                    '?' => TokenKind::Question,
                    '\'' => TokenKind::SingleQuote,
                    '"' => TokenKind::DoubleQuote,

                    '_' => match self.first() {
                        c if is_valid_id_char(c) => self.keyword_or_ident('_'),
                        _ => TokenKind::Underscore,
                    },

                    '-' => match self.first() {
                        '>' => {
                            self.consume_chars(1);
                            TokenKind::Arrow
                        }
                        _ => TokenKind::Minus,
                    },

                    ':' => match self.first() {
                        ':' => {
                            self.consume_chars(1);
                            TokenKind::DoubleColon
                        }
                        _ => TokenKind::Colon,
                    },
                    '.' => match (self.first(), self.second()) {
                        ('.', '.') => {
                            self.consume_chars(2);
                            TokenKind::Ellipsis
                        }
                        ('.', '<') => {
                            self.consume_chars(2);
                            TokenKind::RangeExclusive
                        }
                        ('.', '=') => {
                            self.consume_chars(2);
                            TokenKind::RangeInclusive
                        }
                        _ => TokenKind::Dot,
                    },
                    '=' => match self.first() {
                        '>' => {
                            self.consume_chars(1);
                            TokenKind::FatArrow
                        }
                        _ => TokenKind::Equals,
                    },
                    '/' => match self.first() {
                        '/' => {
                            let marker = self.second();
                            let doc_style = matches!(marker, '/' | '!');
                            self.next_char(); // consume the first '/'
                            if doc_style {
                                self.next_char();
                            }
                            let kind = if doc_style {
                                if marker == '!' {
                                    CommentKind::ModuleDoc
                                } else {
                                    CommentKind::Doc
                                }
                            } else {
                                CommentKind::Line
                            };
                            let com = TokenKind::Comment {
                                content: self
                                    .next_char_while(None, |c| c != '\n')
                                    .trim()
                                    .to_owned(),
                                kind,
                            };
                            // consume the newline character
                            self.next_char();
                            com
                        }
                        _ => TokenKind::Slash,
                    },

                    '0' if self.first() == 'b' => {
                        // binary literal
                        self.consume_chars(1);
                        let value = self.number();
                        let (suffix, _) = self.suffix();
                        TokenKind::Integer {
                            value,
                            suffix,
                            base: IntegerBase::Binary,
                        }
                    }

                    '0' if self.first() == 'x' => {
                        // hex literal
                        self.consume_chars(1);
                        let value = self.hex();
                        let (suffix, _) = self.suffix();
                        TokenKind::Integer {
                            value,
                            suffix,
                            base: IntegerBase::Hex,
                        }
                    }

                    '0' if self.first() == 'o' => {
                        // octal literal
                        self.consume_chars(1);
                        let value = self.octal();
                        let (suffix, _) = self.suffix();
                        TokenKind::Integer {
                            value,
                            suffix,
                            base: IntegerBase::Octal,
                        }
                    }

                    '\\' if self.first() == 'u' => {
                        // unicode escape sequence
                        self.consume_chars(1);
                        TokenKind::UnicodeEscSeq(self.hex())
                    }

                    // keywords/identifiers
                    c if c == '_' || c.is_alphabetic() => self.keyword_or_ident(c),

                    // numbers
                    c @ '0'..='9' => {
                        // [0-9]+
                        let mut value = c.to_string() + &self.number();
                        let mut is_float = false;

                        // (.[0-9]+)?
                        match (self.first(), self.second()) {
                            ('.', '0'..='9') => {
                                // consume '.' and parse the floating point
                                is_float = true;
                                value = value + &self.next_char_str().unwrap() + &self.number()
                            }
                            _ => (),
                        }

                        match self.first() {
                            'e' | 'E' => {
                                // consume 'e' | 'E'
                                is_float = true;
                                value += &self.next_char_str().unwrap();
                                match self.first() {
                                    '-' | '+' => value += &self.next_char_str().unwrap(),
                                    _ => (),
                                }
                                value += &self.number()
                            }
                            _ => (),
                        }

                        let (suffix, f) = self.suffix();
                        is_float |= f;

                        if is_float {
                            TokenKind::Float { value, suffix }
                        } else {
                            TokenKind::Integer {
                                value,
                                suffix,
                                base: IntegerBase::Decimal,
                            }
                        }
                    }
                    _ => TokenKind::Illegal(self.next_str()),
                };

                let end = self.stash_pos;
                return Token {
                    kind,
                    span: Span { start, end },
                };
            }
        }

        self.eof()
    }

    fn ensure_tokens(&mut self, n: usize) {
        if self.token_stash.len() < n {
            for _ in self.token_stash.len()..n {
                let tok = self.next_token();
                self.token_stash.push_back(tok);
                if self.is_eof() {
                    break;
                }
            }
        }
    }

    fn next_preceding(&mut self) -> Vec<Preceding> {
        let mut preceding = vec![];
        loop {
            if let Some(t) = self.take_token_if(is_tok_comment) {
                preceding.push(Preceding::Comment(t))
            } else if let Some(t) = self.take_token_if(is_tok_whitespace) {
                preceding.push(Preceding::Whitespace(t))
            } else {
                break;
            }
        }

        preceding
    }

    fn get_token(&mut self) -> &Token {
        self.ensure_tokens(1);
        self.token_stash.front().unwrap()
    }

    fn take_token(&mut self) -> Token {
        self.ensure_tokens(1);
        let tok = self.token_stash.pop_front().unwrap();
        self.last_tok_span = tok.span;
        tok
    }

    fn take_token_if(&mut self, f: impl Fn(&Token) -> bool) -> Option<Token> {
        if f(self.get_token()) {
            Some(self.take_token())
        } else {
            None
        }
    }

    fn rewind_tokens(&mut self) {
        if self.stash.len() != 0 {
            self.stash_pos = self.curr_pos;
        }

        // after resetting the index and position, clear the stash
        self.stash.clear();
        self.token_stash.clear();
    }

    fn ensure_stash(&mut self, n: usize) {
        while self.stash.len() < n {
            let p = self.next_preceding();
            let t = self.take_token();
            self.stash.push_back((p, t));
        }
    }

    pub fn consume(&mut self) -> (Vec<Preceding>, Token) {
        // consume the preceding whitespace/comments and last token
        let (mut prec_w_tok, _) = self.consume_count(1);
        prec_w_tok.remove(0)
    }

    pub fn consume_count(&mut self, n: usize) -> (Vec<(Vec<Preceding>, Token)>, Span) {
        // consume the preceding whitespace/comments and token n times
        self.ensure_stash(n);
        let toks = self.stash.drain(0..n).collect::<Vec<_>>();
        let start = if let Some((_, tok)) = toks.first() {
            tok.span.start
        } else {
            self.position()
        };

        let end = if let Some((_, tok)) = toks.last() {
            tok.span.end
        } else {
            start
        };

        self.curr_pos = end;
        (toks, Span { start, end })
    }

    pub fn position(&self) -> Pos {
        self.curr_pos
    }

    pub fn peek_token(&mut self) -> &Token {
        self.peek_token_at(0)
    }

    pub fn peek_token_at(&mut self, idx: usize) -> &Token {
        self.ensure_stash(idx + 1);
        // note: this will always unwrap, because we've called ensure stash
        self.stash.get(idx).map(|(_, t)| t).unwrap()
    }

    pub fn token(&mut self) -> Token {
        let (_, tok) = self.consume();
        tok
    }

    pub fn preceding(&mut self) -> Vec<Preceding> {
        self.stash
            .front_mut()
            .map_or_else(|| vec![], |(p, _)| p.drain(..).collect())
    }

    pub fn peek_preceding(&mut self) -> Vec<&Preceding> {
        self.ensure_stash(1);
        self.stash
            .front()
            .map(|(p, _)| p.iter().collect())
            .unwrap_or_default()
    }
}

/// Convenience helper that runs the lexer to completion and collects all lexemes,
/// including the trailing EOF token, along with their leading trivia.
pub fn lexemes(src: &str) -> Vec<Lexeme> {
    let mut lexer = Lexer::new(src);
    let mut out = Vec::new();

    loop {
        let (leading, token) = lexer.consume();
        let is_eof = matches!(token.kind, TokenKind::EOF);
        out.push(Lexeme { leading, token });
        if is_eof {
            break;
        }
    }

    out
}

#[cfg(test)]
mod lexer_tests {
    use crate::ast::token::{CommentKind, TokenKind};

    use super::{Lexer, Preceding, lexemes};

    #[test]
    fn test_rewind() {
        let mut lex = Lexer::new("fn foo(a: 'a) -> int");
        while !lex.is_eof() {
            let t = lex.token();
            println!("{:?}", t);
        }
    }

    #[test]
    fn test_char() {
        let mut lex = Lexer::new("i = 'a'\nj = \"bf12&&`81----==123=\"\nk = zzzz");
        while !lex.is_eof() {
            let t = lex.token();
            if t.kind == TokenKind::DoubleQuote {
                let (s, _) = lex.quoted_string('"');
                println!("STRING: {}", s);
            } else {
                println!("{:?}", t);
            }
        }
    }

    #[test]
    fn lexemes_collects_tokens() {
        let tokens = lexemes("fn answer() -> i32 { 42 }");
        assert!(!tokens.is_empty());
        assert!(matches!(tokens.last().unwrap().token.kind, TokenKind::EOF));
    }

    #[test]
    fn lexemes_preserve_trivia_and_kinds() {
        let source = "fn foo(mut value: i32) {\n    // answer\n    42\n}\n";
        let tokens = lexemes(source);

        assert!(matches!(tokens[0].token.kind, TokenKind::Fn));
        assert!(matches!(
            tokens[1].token.kind,
            TokenKind::Identifier(ref name) if name == "foo"
        ));
        assert!(matches!(tokens[2].token.kind, TokenKind::LeftParen));
        assert!(matches!(tokens[3].token.kind, TokenKind::Mut));
        assert!(matches!(
            tokens[4].token.kind,
            TokenKind::Identifier(ref name) if name == "value"
        ));
        assert!(matches!(tokens[5].token.kind, TokenKind::Colon));
        assert!(matches!(
            tokens[6].token.kind,
            TokenKind::Identifier(ref name) if name == "i32"
        ));
        assert!(matches!(tokens[7].token.kind, TokenKind::RightParen));
        assert!(matches!(tokens[8].token.kind, TokenKind::LeftCurly));
        assert!(matches!(
            tokens[9].token.kind,
            TokenKind::Integer { ref value, base, .. }
                if value == "42" && matches!(base, crate::ast::token::IntegerBase::Decimal)
        ));
        assert!(matches!(tokens[10].token.kind, TokenKind::RightCurly));
        assert!(matches!(tokens.last().unwrap().token.kind, TokenKind::EOF));

        // The integer is preceded by a comment that we should surface via trivia.
        let comment = tokens[9]
            .leading
            .iter()
            .find_map(|preceding| match preceding {
                Preceding::Comment(tok) => Some(tok),
                _ => None,
            })
            .expect("expected comment preceding integer literal");

        if let TokenKind::Comment {
            ref content,
            ref kind,
        } = comment.kind
        {
            assert_eq!(content, "answer");
            assert_eq!(*kind, CommentKind::Line);
        } else {
            panic!("expected token kind comment");
        }
    }

    #[test]
    fn lexemes_classifies_doc_comment_kinds() {
        let tokens = lexemes("//! module docs\n/// fn docs\nfn main() {}");

        let leading = &tokens[0].leading;
        assert_eq!(leading.len(), 2);
        match &leading[0] {
            Preceding::Comment(token) => {
                assert_eq!(
                    token.kind,
                    TokenKind::Comment {
                        content: "module docs".to_string(),
                        kind: CommentKind::ModuleDoc,
                    }
                );
            }
            other => panic!("unexpected preceding token: {:?}", other),
        }

        match &leading[1] {
            Preceding::Comment(token) => {
                assert_eq!(
                    token.kind,
                    TokenKind::Comment {
                        content: "fn docs".to_string(),
                        kind: CommentKind::Doc,
                    }
                );
            }
            other => panic!("unexpected preceding token: {:?}", other),
        }
    }
}

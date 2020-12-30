use crate::ast::token::{IntegerBase, Token, TokenKind};
use crate::ast::Modifier;
use crate::span::{Pos, Span};

use std::collections::VecDeque;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Preceding {
    Whitespace(Token),
    Comment(Token),
}

pub struct Lexer {
    src: Vec<char>,
    curr_idx: usize,
    curr_pos: Pos,
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
            curr_idx: 0,
            curr_pos: Pos::new(),
            last_tok_span: Span::new(),
            token_stash: VecDeque::new(),
            stash: VecDeque::new(),
        }
    }

    pub fn is_eof(&mut self) -> bool {
        self.src.get(self.curr_idx).is_none()
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
        let ch = self.char_at(self.curr_idx)?;
        if ch == '\n' {
            self.curr_pos.lineno += 1;
            self.curr_pos.col = 0;
        } else {
            self.curr_pos.col += 1;
        }
        self.curr_pos.offset += 1;
        self.curr_idx += 1;
        Some(ch)
    }

    fn next_char_str(&mut self) -> Option<String> {
        self.next_char().map(|c| c.to_string())
    }

    fn first(&self) -> char {
        self.char_at(self.curr_idx).unwrap_or('\0')
    }

    fn second(&self) -> char {
        self.char_at(self.curr_idx + 1).unwrap_or('\0')
    }

    fn consume_chars(&mut self, n: usize) {
        // consume `n` characters
        for _ in 0..n {
            self.next_char();
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

    fn quoted_string(&mut self, quote: char) -> (String, bool) {
        let mut s = String::new();
        while let Some(ch) = self.next_char() {
            match ch {
                c if c == quote => {
                    return (s, true);
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
            "protocol" => TokenKind::Protocol,
            "impl" => TokenKind::Impl,
            "type" => TokenKind::Type,
            "with" => TokenKind::With,
            "import" => TokenKind::Import,
            "as" => TokenKind::As,
            "for" => TokenKind::For,
            "while" => TokenKind::While,
            "loop" => TokenKind::Loop,
            "in" => TokenKind::In,
            "is" => TokenKind::Is,
            "pub" => TokenKind::Modifier(Modifier::Pub),
            "static" => TokenKind::Modifier(Modifier::Static),
            "hidden" => TokenKind::Modifier(Modifier::Hidden),
            "internal" => TokenKind::Modifier(Modifier::Internal),
            "unsafe" => TokenKind::Modifier(Modifier::Unsafe),
            "nil" => TokenKind::Nil,
            "true" => TokenKind::Bool(true),
            "false" => TokenKind::Bool(false),
            _ => TokenKind::Identifier(id),
        }
    }

    fn next_token(&mut self) -> Token {
        let start = self.curr_pos;
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
                            let doc_style = self.second() == '/';
                            self.next_char(); // consume the first '/'
                            if doc_style {
                                self.next_char();
                            }
                            let com = TokenKind::Comment {
                                content: self
                                    .next_char_while(None, |c| c != '\n')
                                    .trim()
                                    .to_owned(),
                                doc_style,
                            };
                            // consume the newline character
                            self.next_char();
                            com
                        }
                        _ => TokenKind::Slash,
                    },

                    // literals
                    'b' => match self.first() {
                        '"' => {
                            let (value, terminated) = self.quoted_string('"');
                            TokenKind::ByteString { value, terminated }
                        }
                        '\'' => {
                            let (value, terminated) = self.quoted_string('\'');
                            TokenKind::Byte { value, terminated }
                        }
                        _ => self.keyword_or_ident('b'),
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

                    '"' => {
                        let (value, terminated) = self.quoted_string('"');
                        TokenKind::String { value, terminated }
                    }

                    '\'' => {
                        let (value, terminated) = self.quoted_string('\'');
                        TokenKind::Char { value, terminated }
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

                let end = self.curr_pos;
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
        let start = self.position();
        self.ensure_stash(n);
        let toks = self.stash.drain(0..n).collect::<Vec<_>>();
        let end = if let Some((_, tok)) = toks.last() {
            tok.span.end
        } else {
            start
        };
        (toks, Span { start, end })
    }

    pub fn position(&mut self) -> Pos {
        if self.is_eof() {
            self.curr_pos
        } else {
            self.peek_token().span.start
        }
    }

    pub fn prev_position(&self) -> Pos {
        self.last_tok_span.start
    }

    pub fn peek_token(&mut self) -> &Token {
        self.peek_token_at(0)
    }

    pub fn peek_token_at(&mut self, idx: usize) -> &Token {
        self.ensure_stash(idx + 1);
        // note: this will always unwrap, because we've called ensure stash
        self.stash.get(idx).map(|(_, t)| t).unwrap()
    }

    // pub fn peek_forward(&mut self, find_tok: TokenKind, stop_tok: TokenKind) -> usize {
    //     let mut idx = 0;
    //     let tok = self.peek_token_at(idx);
    //     while !self.is_eof() && tok.kind != find_tok && tok.kind != stop_tok {
    //         idx += 1;
    //         self.peek_token_at(idx);
    //     }
    // }

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

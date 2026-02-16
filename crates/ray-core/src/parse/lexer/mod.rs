use crate::ast::{
    Modifier,
    token::{CommentKind, IntegerBase, Token, TokenKind},
};
use ray_shared::span::{Pos, Span};

use std::collections::VecDeque;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Preceding {
    Whitespace(Token, usize),
    Comment(Token, usize),
}

/// A single lexeme produced by the Ray lexer along with any leading trivia.
#[derive(Clone, Debug)]
pub struct Lexeme {
    pub leading: Vec<Preceding>,
    pub token: Token,
}

pub struct StashEntry {
    pub preceding: Vec<Preceding>,
    pub token: Token,
    pub char_idx: usize,
}

pub struct Lexer {
    src: Vec<char>,
    curr_pos: Pos,
    stash_pos: Pos,
    /// Character index into `src` corresponding to `curr_pos`.
    /// Separate from `Pos::offset` which tracks byte offsets.
    curr_char_idx: usize,
    /// Character index into `src` corresponding to `stash_pos`.
    stash_char_idx: usize,
    last_tok_span: Span,
    token_stash: VecDeque<Token>,
    stash: VecDeque<StashEntry>,
    newline_mode: NewlineMode,
    /// Comments collected by `next_preceding` that were deferred past a
    /// newline token in Emit mode. Prepended to the next `next_preceding` call
    /// so they end up on the next non-newline token.
    deferred_preceding: Vec<Preceding>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NewlineMode {
    Emit,
    Suppress,
}

/// A segment returned by the f-string lexer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FStringSegment {
    /// A run of literal characters (escapes and `{{`/`}}` already processed).
    Literal(String),
    /// A bare `{` was encountered — the caller should parse an expression.
    ExprStart,
    /// The closing quote was reached.
    End,
    /// EOF before the closing quote.
    Unterminated,
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
            curr_char_idx: 0,
            stash_char_idx: 0,
            last_tok_span: Span::new(),
            token_stash: VecDeque::new(),
            stash: VecDeque::new(),
            newline_mode: NewlineMode::Suppress,
            deferred_preceding: vec![],
        }
    }

    pub fn set_newline_mode(&mut self, mode: NewlineMode) {
        self.newline_mode = mode;
    }

    pub fn newline_mode(&self) -> NewlineMode {
        self.newline_mode
    }

    pub fn is_eof(&self) -> bool {
        self.src.get(self.stash_char_idx).is_none()
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
        let ch = self.char_at(self.stash_char_idx)?;
        if ch == '\n' {
            self.stash_pos.lineno += 1;
            self.stash_pos.col = 0;
        } else {
            self.stash_pos.col += 1;
        }
        self.stash_char_idx += 1;
        self.stash_pos.offset += ch.len_utf8();
        Some(ch)
    }

    fn next_char_str(&mut self) -> Option<String> {
        self.next_char().map(|c| c.to_string())
    }

    fn first(&self) -> char {
        self.char_at(self.stash_char_idx).unwrap_or('\0')
    }

    fn second(&self) -> char {
        self.char_at(self.stash_char_idx + 1).unwrap_or('\0')
    }

    fn consume_char(&mut self) -> Option<char> {
        let c = self.next_char();
        self.curr_pos = self.stash_pos;
        self.curr_char_idx = self.stash_char_idx;
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

    /// Read the next segment of an f-string. Must be called after the opening
    /// `"` has been consumed. Returns one segment at a time:
    ///
    /// - `Literal(s)` — a run of literal characters (escapes processed,
    ///   `{{`/`}}` collapsed to `{`/`}`)
    /// - `ExprStart` — a bare `{` was encountered; the caller should parse an
    ///   expression and then expect `}`
    /// - `End` — the closing quote was reached
    /// - `Unterminated` — EOF before the closing quote
    pub fn next_fstring_segment(&mut self, quote: char) -> FStringSegment {
        self.rewind_tokens();

        let mut s = String::new();
        loop {
            let saved_pos = self.stash_pos;
            let saved_char_idx = self.stash_char_idx;
            let Some(ch) = self.next_char() else { break };
            match ch {
                c if c == quote => {
                    if !s.is_empty() {
                        // Put back the closing quote so the next call returns End.
                        self.stash_pos = saved_pos;
                        self.stash_char_idx = saved_char_idx;
                        return FStringSegment::Literal(s);
                    }
                    return FStringSegment::End;
                }
                '{' if self.first() == '{' => {
                    // escaped `{{` → literal `{`
                    self.next_char();
                    s.push('{');
                }
                '{' => {
                    if !s.is_empty() {
                        // Put back the `{` so the next call returns ExprStart.
                        self.stash_pos = saved_pos;
                        self.stash_char_idx = saved_char_idx;
                        return FStringSegment::Literal(s);
                    }
                    return FStringSegment::ExprStart;
                }
                '}' if self.first() == '}' => {
                    // escaped `}}` → literal `}`
                    self.next_char();
                    s.push('}');
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
        if !s.is_empty() {
            return FStringSegment::Literal(s);
        }
        FStringSegment::Unterminated
    }

    /// Commit the current character-reading position so that normal
    /// tokenisation resumes from here. Called after `next_fstring_segment`
    /// returns `ExprStart` to switch from character mode back to token mode.
    pub fn commit_position(&mut self) {
        self.curr_pos = self.stash_pos;
        self.curr_char_idx = self.stash_char_idx;
        self.stash.clear();
        self.token_stash.clear();
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
            "continue" => TokenKind::Continue,
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
            "new" => TokenKind::New,
            "box" => TokenKind::Bx,
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
                    '\n' => match self.newline_mode {
                        NewlineMode::Emit => TokenKind::NewLine,
                        NewlineMode::Suppress => TokenKind::Whitespace,
                    },
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
                                    .trim_end()
                                    .to_owned(),
                                kind,
                            };
                            if self.newline_mode == NewlineMode::Suppress {
                                // When suppressing newlines we eagerly consume the trailing
                                // line break so callers continue seeing only trivia.
                                self.next_char();
                            }
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

    fn promote_pending_newline(&mut self) {
        if self.newline_mode != NewlineMode::Emit {
            return;
        }

        loop {
            let newline_token = self.stash.front_mut().and_then(|entry| {
                entry
                    .preceding
                    .iter()
                    .position(|p| match p {
                        Preceding::Whitespace(tok, _) => {
                            tok.kind == TokenKind::NewLine || tok.span.lines() > 1
                        }
                        _ => false,
                    })
                    .and_then(|idx| match entry.preceding.remove(idx) {
                        Preceding::Whitespace(mut tok, char_idx) => {
                            tok.kind = TokenKind::NewLine;
                            Some((tok, char_idx))
                        }
                        _ => None,
                    })
            });
            let Some((token, char_idx)) = newline_token else {
                break;
            };

            log::debug!(
                "[lexer] promote_pending_newline: injecting {:?}",
                token.span
            );
            self.stash.push_front(StashEntry {
                preceding: Vec::new(),
                token,
                char_idx,
            });
        }
    }

    fn next_preceding(&mut self) -> Vec<Preceding> {
        let mut preceding = std::mem::take(&mut self.deferred_preceding);
        loop {
            if let Some(t) = self.take_token_if(is_tok_comment) {
                preceding.push(Preceding::Comment(t, self.stash_char_idx))
            } else {
                // When newline emission is enabled we must leave newline tokens
                // in the main stream so the parser can treat them as statement
                // terminators. If we've already collected comments, defer them
                // past this newline so they end up on the next non-newline token.
                if self.newline_mode == NewlineMode::Emit
                    && matches!(self.get_token().kind, TokenKind::NewLine)
                {
                    let has_comments = preceding
                        .iter()
                        .any(|p| matches!(p, Preceding::Comment(..)));
                    if has_comments {
                        self.deferred_preceding = preceding;
                        return vec![];
                    }
                    break;
                }

                if let Some(t) = self.take_token_if(is_tok_whitespace) {
                    log::debug!("[lexer] next_preceding: consuming whitespace {:?}", t.span);
                    preceding.push(Preceding::Whitespace(t, self.stash_char_idx))
                } else {
                    break;
                }
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
            self.stash_char_idx = self.curr_char_idx;
        }

        // after resetting the index and position, clear the stash
        self.stash.clear();
        self.token_stash.clear();
        self.deferred_preceding.clear();
    }

    fn ensure_stash(&mut self, n: usize) {
        while self.stash.len() < n {
            self.promote_pending_newline();
            let preceding = self.next_preceding();
            let token = self.take_token();
            self.stash.push_back(StashEntry {
                preceding,
                token,
                char_idx: self.stash_char_idx,
            });
        }
        self.promote_pending_newline();
    }

    pub fn consume(&mut self) -> StashEntry {
        // consume the preceding whitespace/comments and last token
        let (mut prec_w_tok, _) = self.consume_count(1);
        prec_w_tok.remove(0)
    }

    pub fn consume_count(&mut self, n: usize) -> (Vec<StashEntry>, Span) {
        // consume the preceding whitespace/comments and token n times
        self.ensure_stash(n);
        let toks = self.stash.drain(0..n).collect::<Vec<_>>();
        let (start, start_char_idx) = if let Some(StashEntry {
            token, char_idx, ..
        }) = toks.first()
        {
            (token.span.start, *char_idx)
        } else {
            (self.position(), self.curr_char_idx)
        };

        let (end, end_char_idx) = if let Some(StashEntry {
            token, char_idx, ..
        }) = toks.last()
        {
            (token.span.end, *char_idx)
        } else {
            (start, start_char_idx)
        };

        self.curr_pos = end;
        self.curr_char_idx = end_char_idx;
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
        self.stash.get(idx).map(|entry| &entry.token).unwrap()
    }

    pub fn token(&mut self) -> Token {
        let StashEntry { token, .. } = self.consume();
        token
    }

    pub fn preceding(&mut self) -> Vec<Preceding> {
        self.stash
            .front_mut()
            .map_or_else(|| vec![], |entry| entry.preceding.drain(..).collect())
    }

    pub fn peek_preceding(&mut self) -> Vec<&Preceding> {
        self.ensure_stash(1);
        self.stash
            .front()
            .map(|entry| entry.preceding.iter().collect())
            .unwrap_or_default()
    }
}

#[cfg(test)]
mod tests {
    use crate::{ast::token::TokenKind, parse::Lexer};

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

    /// Helper: collect all tokens from source, returning (kind, start_offset, end_offset).
    fn tokens(src: &str) -> Vec<(TokenKind, usize, usize)> {
        let mut lex = Lexer::new(src);
        let mut out = vec![];
        while !lex.is_eof() {
            let t = lex.token();
            if t.kind == TokenKind::EOF {
                break;
            }
            out.push((t.kind, t.span.start.offset, t.span.end.offset));
        }
        out
    }

    /// Verify that every token span can be used to slice the source string
    /// without panicking, and that the slice matches the expected text.
    fn assert_spans_are_valid_byte_offsets(src: &str) {
        let mut lex = Lexer::new(src);
        while !lex.is_eof() {
            let t = lex.token();
            if t.kind == TokenKind::EOF {
                break;
            }
            let start = t.span.start.offset;
            let end = t.span.end.offset;
            assert!(
                src.is_char_boundary(start),
                "start offset {} is not a char boundary in {:?} (token {:?})",
                start,
                src,
                t.kind
            );
            assert!(
                src.is_char_boundary(end),
                "end offset {} is not a char boundary in {:?} (token {:?})",
                end,
                src,
                t.kind
            );
            assert!(
                end >= start,
                "end {} < start {} for token {:?}",
                end,
                start,
                t.kind
            );
            // Slicing must not panic.
            let _slice = &src[start..end];
        }
    }

    #[test]
    fn ascii_offsets_equal_char_indices() {
        let src = "fn foo(x: int) -> int";
        let toks = tokens(src);
        // "fn" starts at byte 0, ends at byte 2
        assert_eq!(toks[0], (TokenKind::Fn, 0, 2));
        // "foo" starts at byte 3, ends at byte 6
        assert_eq!(toks[1], (TokenKind::Identifier("foo".to_string()), 3, 6));
        assert_spans_are_valid_byte_offsets(src);
    }

    #[test]
    fn multibyte_comment_offsets_are_byte_based() {
        // The em dash '—' is 3 bytes in UTF-8.
        let src = "// a — b\nx = 1";
        assert_spans_are_valid_byte_offsets(src);

        let toks = tokens(src);
        // After the comment (which includes '—'), the next line starts.
        // "// a — b" is 10 bytes: '/' '/' ' ' 'a' ' ' '—'(3) ' ' 'b' = 10
        // Plus '\n' = 11
        // "x" should start at byte 11.
        let x_tok = toks
            .iter()
            .find(|(k, _, _)| *k == TokenKind::Identifier("x".to_string()))
            .expect("should find 'x' token");
        assert_eq!(x_tok.1, 11, "x should start at byte 11");
    }

    #[test]
    fn multibyte_in_identifier_context() {
        // CJK character '中' is 3 bytes in UTF-8.
        // The lexer treats it as an identifier character (alphabetic).
        let src = "x = 中";
        assert_spans_are_valid_byte_offsets(src);

        let toks = tokens(src);
        // 'x' at 0..1, '=' at 2..3, '中' at 4..7 (3 bytes)
        let last = toks.last().unwrap();
        assert_eq!(last.1, 4, "中 should start at byte 4");
        assert_eq!(last.2, 7, "中 should end at byte 7");
    }

    #[test]
    fn multiple_multibyte_chars_accumulate_correctly() {
        // Each '—' is 3 bytes. After two of them (6 bytes), offsets should reflect that.
        let src = "// —— done\nx = 1";
        assert_spans_are_valid_byte_offsets(src);

        let toks = tokens(src);
        // "// —— done" = '/' '/' ' ' '—'(3) '—'(3) ' ' 'd' 'o' 'n' 'e' = 14 bytes
        // Plus '\n' = 15
        let x_tok = toks
            .iter()
            .find(|(k, _, _)| *k == TokenKind::Identifier("x".to_string()))
            .expect("should find 'x' token");
        assert_eq!(x_tok.1, 15, "x should start at byte 15");
    }

    #[test]
    fn emoji_in_comment() {
        // '🎉' is 4 bytes in UTF-8.
        let src = "// 🎉\nx = 1";
        assert_spans_are_valid_byte_offsets(src);

        let toks = tokens(src);
        // "// 🎉" = '/' '/' ' ' '🎉'(4) = 7 bytes, plus '\n' = 8
        let x_tok = toks
            .iter()
            .find(|(k, _, _)| *k == TokenKind::Identifier("x".to_string()))
            .expect("should find 'x' token");
        assert_eq!(x_tok.1, 8, "x should start at byte 8");
    }

    #[test]
    fn doc_comment_with_multibyte() {
        // This is the pattern that caused the original LSP crash.
        let src = "/// `'a` — Left operand type.\nfn add() => 1";
        assert_spans_are_valid_byte_offsets(src);

        let toks = tokens(src);
        // "/// `'a` — Left operand type." = 31 bytes (— is 3 bytes, rest ASCII)
        // Plus '\n' = 32
        let fn_tok = toks
            .iter()
            .find(|(k, _, _)| *k == TokenKind::Fn)
            .expect("should find 'fn' token");
        assert_eq!(fn_tok.1, 32, "fn should start at byte 32");
    }

    #[test]
    fn module_doc_comment_with_multibyte() {
        let src = "//! Module — overview\nfn x() => 1";
        assert_spans_are_valid_byte_offsets(src);

        let toks = tokens(src);
        // "//! Module — overview" = 23 bytes (— is 3 bytes)
        // Plus '\n' = 24
        let fn_tok = toks
            .iter()
            .find(|(k, _, _)| *k == TokenKind::Fn)
            .expect("should find 'fn' token");
        assert_eq!(fn_tok.1, 24, "fn should start at byte 24");
    }

    #[test]
    fn string_slicing_with_multibyte_offsets() {
        // The key invariant: span offsets can be used to slice the original source.
        let src = "/// Type — desc\nfn foo(x: int) -> int => x";
        let mut lex = Lexer::new(src);
        while !lex.is_eof() {
            let t = lex.token();
            if t.kind == TokenKind::EOF {
                break;
            }
            let slice = &src[t.span.start.offset..t.span.end.offset];
            match &t.kind {
                TokenKind::Fn => assert_eq!(slice, "fn"),
                TokenKind::Identifier(s) => assert_eq!(slice, s.as_str()),
                TokenKind::Arrow => assert_eq!(slice, "->"),
                TokenKind::FatArrow => assert_eq!(slice, "=>"),
                _ => {}
            }
        }
    }
}

use crate::{
    ast::{Path, TrailingPolicy, ValueKind, token::TokenKind},
    parse::{Parser, lexer::NewlineMode, parser::Restrictions},
    span::Pos,
};

pub(crate) struct ParseScope<'a, 'src> {
    pub(crate) p: &'a mut Parser<'src>,
    pub(crate) undo: Vec<Undo>,
    pub(crate) ctx: ParseContext,
}

#[derive(Clone, Debug)]
pub struct ParseContext {
    pub path: Path,
    pub restrictions: Restrictions,
    pub description: Option<String>,
    pub anchor: Option<Pos>,
    pub stop_token: Option<TokenKind>,
}

pub(crate) enum Undo {
    Newline(NewlineMode),
}

pub(crate) struct SeqSpec {
    pub(crate) delimiters: Option<(TokenKind, TokenKind)>,
    pub(crate) trailing: TrailingPolicy,
    pub(crate) newline: NewlineMode,
    pub(crate) restrictions: Restrictions,
}

impl<'a, 'src> std::ops::Deref for ParseScope<'a, 'src> {
    type Target = Parser<'src>;
    fn deref(&self) -> &Self::Target {
        self.p
    }
}

impl<'a, 'src> std::ops::DerefMut for ParseScope<'a, 'src> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.p
    }
}

impl<'a, 'src> ParseScope<'a, 'src> {
    // chainable ctx mutators
    pub fn with_restrictions(mut self, r: Restrictions) -> Self {
        self.ctx.restrictions |= r;
        self
    }

    pub fn with_description(mut self, s: impl Into<String>) -> Self {
        let desc = s.into();
        log::debug!("new context: {}", desc);
        self.ctx.description = Some(desc);
        self
    }

    pub fn with_path(mut self, p: Path) -> Self {
        self.ctx.path = p;
        self
    }

    pub fn stopping_at(mut self, k: TokenKind) -> Self {
        self.ctx.stop_token = Some(k);
        self
    }

    // chainable lexer/plumbing mutators (record undo)
    pub fn with_newline_mode(mut self, mode: NewlineMode) -> Self {
        let prev = self.p.lex.newline_mode();
        log::debug!(
            "[with_newline_mode] changing mode from {:?} -> {:?}",
            prev,
            mode
        );
        self.p.lex.set_newline_mode(mode);
        self.undo.push(Undo::Newline(prev));
        self
    }

    // access to the working ctx
    pub fn ctx(&self) -> &ParseContext {
        &self.ctx
    }

    pub fn ctx_clone(&self) -> ParseContext {
        self.ctx.clone()
    }
}

impl<'a, 'src> Drop for ParseScope<'a, 'src> {
    fn drop(&mut self) {
        while let Some(u) = self.undo.pop() {
            match u {
                Undo::Newline(prev) => {
                    let curr = self.p.lex.newline_mode();
                    log::debug!(
                        "[ParseScope::drop] undoing newline mode from {:?} -> {:?}",
                        curr,
                        prev,
                    );
                    self.p.lex.set_newline_mode(prev);
                }
            }
        }
    }
}

impl ParseContext {
    pub fn new(path: Path) -> ParseContext {
        ParseContext {
            path,
            restrictions: Restrictions::empty(),
            description: None,
            anchor: None,
            stop_token: None,
        }
    }

    pub fn get_vkind(&self) -> ValueKind {
        if self.restrictions.contains(Restrictions::RVALUE) {
            ValueKind::RValue
        } else {
            ValueKind::LValue
        }
    }
}

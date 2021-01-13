use super::{CurlyElementKind, Expr, ExprKind, Module};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Visitor<'a, I>
where
    I: Iterator<Item = &'a Expr>,
{
    stack: Vec<&'a Expr>,
    stmt_iter: I,
}

impl<'a, I> Iterator for Visitor<'a, I>
where
    I: Iterator<Item = &'a Expr>,
{
    type Item = &'a Expr;

    fn next(&mut self) -> Option<&'a Expr> {
        if let Some(ex) = self.stack.pop() {
            self.add_children(ex);
            Some(ex)
        } else if let Some(ex) = self.stmt_iter.next() {
            self.add_children(ex);
            Some(ex)
        } else {
            None
        }
    }
}

impl<'a> From<&'a Module> for Visitor<'a, std::slice::Iter<'a, Expr>> {
    fn from(module: &'a Module) -> Visitor<'a, std::slice::Iter<'a, Expr>> {
        Visitor {
            stack: vec![],
            stmt_iter: module.stmts.iter(),
        }
    }
}

impl<'a> From<&'a Expr> for Visitor<'a, std::vec::IntoIter<&'a Expr>> {
    fn from(ex: &'a Expr) -> Visitor<'a, std::vec::IntoIter<&Expr>> {
        Visitor {
            stack: vec![],
            stmt_iter: vec![ex].into_iter(),
        }
    }
}

impl<'a, I> Visitor<'a, I>
where
    I: Iterator<Item = &'a Expr>,
{
    fn add_children(&mut self, ex: &'a Expr) {
        match &ex.kind {
            ExprKind::Break(val) => {
                if let Some(val) = val {
                    self.stack.push(val);
                }
            }

            ExprKind::Assign(assign) => {
                self.stack.push(&assign.lhs);
                self.stack.push(&assign.rhs);
            }
            ExprKind::Block(block) => {
                self.stack.extend(block.stmts.iter());
            }
            ExprKind::BinOp(binop) => {
                self.stack.push(&binop.lhs);
                self.stack.push(&binop.rhs)
            }
            ExprKind::Call(call) => {
                self.stack.push(&call.lhs);
                self.stack.extend(call.args.items.iter());
            }
            ExprKind::Cast(cast) => self.stack.push(&cast.lhs),
            ExprKind::Closure(closure) => {
                self.stack.extend(closure.args.items.iter());
                self.stack.push(&closure.body);
            }
            ExprKind::Curly(c) => {
                for el in c.elements.iter() {
                    match &el.kind {
                        CurlyElementKind::Labeled(_, e) => self.stack.push(e),
                        _ => (),
                    }
                }
            }
            ExprKind::DefaultValue(default_value) => self.stack.push(&default_value),
            ExprKind::Dot(dot) => self.stack.push(&dot.lhs),
            ExprKind::Fn(fun) => {
                if let Some(body) = &fun.body {
                    self.stack.push(&body);
                }
            }
            ExprKind::For(for_ex) => {
                self.stack.push(&for_ex.expr);
                self.stack.push(&for_ex.body);
            }
            ExprKind::If(if_ex) => {
                self.stack.push(&if_ex.cond);
                self.stack.push(&if_ex.then);
                if let Some(el) = &if_ex.els {
                    self.stack.push(&el)
                }
            }
            ExprKind::Index(index) => self.stack.push(&index.lhs),
            ExprKind::Labeled(_, ex) => self.stack.push(&ex),
            ExprKind::List(l) => self.stack.extend(l.items.iter()),
            ExprKind::Loop(loop_ex) => self.stack.push(&loop_ex.body),
            ExprKind::Paren(paren) => self.stack.push(&paren),
            ExprKind::Return(val) => {
                if let Some(v) = val {
                    self.stack.push(&v)
                }
            }
            ExprKind::Sequence(seq) | ExprKind::Tuple(seq) => self.stack.extend(seq.items.iter()),
            ExprKind::UnaryOp(unary_op) => self.stack.push(&unary_op.expr),
            ExprKind::While(while_ex) => {
                self.stack.push(&while_ex.cond);
                self.stack.push(&while_ex.body)
            }
            ExprKind::Unsafe(ex) => self.stack.push(&ex),
            ExprKind::Literal(_)
            | ExprKind::Name(_)
            | ExprKind::Path(_)
            | ExprKind::Range(_)
            | ExprKind::Type(_) => (),
        }
    }
}

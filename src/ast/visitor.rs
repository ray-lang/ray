// use super::{CurlyElementKind, Expr, Module};

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub struct Visitor<'a, I, T, U>
// where
//     I: Iterator<Item = &'a Expr<T, U>>,
// {
//     stack: Vec<&'a Expr<T, U>>,
//     stmt_iter: I,
// }

// impl<'a, I, T, U> Iterator for Visitor<'a, I, T, U>
// where
//     I: Iterator<Item = &'a Expr<T, U>>,
// {
//     type Item = &'a Expr<T, U>;

//     fn next(&mut self) -> Option<&'a Expr<T, U>> {
//         if let Some(ex) = self.stack.pop() {
//             self.add_children(ex);
//             Some(ex)
//         } else if let Some(ex) = self.stmt_iter.next() {
//             self.add_children(ex);
//             Some(ex)
//         } else {
//             None
//         }
//     }
// }

// impl<'a, T, U> From<&'a Module<T, U>> for Visitor<'a, std::slice::Iter<'a, Expr<T, U>>, T, U> {
//     fn from(module: &'a Module<T, U>) -> Self {
//         Visitor {
//             stack: vec![],
//             stmt_iter: module.stmts.iter(),
//         }
//     }
// }

// impl<'a, T, U> From<&'a Expr<T, U>> for Visitor<'a, std::vec::IntoIter<&'a Expr<T, U>>, T, U> {
//     fn from(ex: &'a Expr<T, U>) -> Self {
//         Visitor {
//             stack: vec![],
//             stmt_iter: vec![ex].into_iter(),
//         }
//     }
// }

// impl<'a, I, T, U> Visitor<'a, I, T, U>
// where
//     I: Iterator<Item = &'a Expr<T, U>>,
// {
//     fn add_children(&mut self, ex: &'a Expr<T, U>) {
//         match &ex.kind {
//             Expr::Break(val) => {
//                 if let Some(val) = val {
//                     self.stack.push(val);
//                 }
//             }

//             Expr::Assign(assign) => {
//                 self.stack.push(&assign.lhs);
//                 self.stack.push(&assign.rhs);
//             }
//             Expr::Block(block) => {
//                 self.stack.extend(block.stmts.iter());
//             }
//             Expr::BinOp(binop) => {
//                 self.stack.push(&binop.lhs);
//                 self.stack.push(&binop.rhs)
//             }
//             Expr::Call(call) => {
//                 self.stack.push(&call.lhs);
//                 self.stack.extend(call.args.items.iter());
//             }
//             Expr::Cast(cast) => self.stack.push(&cast.lhs),
//             Expr::Closure(closure) => {
//                 self.stack.extend(closure.args.items.iter());
//                 self.stack.push(&closure.body);
//             }
//             Expr::Curly(c) => {
//                 for el in c.elements.iter() {
//                     match &el.kind {
//                         CurlyElementKind::Labeled(_, e) => self.stack.push(e),
//                         _ => (),
//                     }
//                 }
//             }
//             Expr::DefaultValue(default_value) => self.stack.push(&default_value),
//             Expr::Dot(dot) => self.stack.push(&dot.lhs),
//             Expr::Fn(fun) => {
//                 if let Some(body) = &fun.body {
//                     self.stack.push(&body);
//                 }
//             }
//             Expr::For(for_ex) => {
//                 self.stack.push(&for_ex.expr);
//                 self.stack.push(&for_ex.body);
//             }
//             Expr::If(if_ex) => {
//                 self.stack.push(&if_ex.cond);
//                 self.stack.push(&if_ex.then);
//                 if let Some(el) = &if_ex.els {
//                     self.stack.push(&el)
//                 }
//             }
//             Expr::Index(index) => self.stack.push(&index.lhs),
//             Expr::Labeled(_, ex) => self.stack.push(&ex),
//             Expr::List(l) => self.stack.extend(l.items.iter()),
//             Expr::Loop(loop_ex) => self.stack.push(&loop_ex.body),
//             Expr::Paren(paren) => self.stack.push(&paren),
//             Expr::Return(val) => {
//                 if let Some(v) = val {
//                     self.stack.push(&v)
//                 }
//             }
//             Expr::Sequence(seq) | Expr::Tuple(seq) => self.stack.extend(seq.items.iter()),
//             Expr::UnaryOp(unary_op) => self.stack.push(&unary_op.expr),
//             Expr::While(while_ex) => {
//                 self.stack.push(&while_ex.cond);
//                 self.stack.push(&while_ex.body)
//             }
//             Expr::Unsafe(ex) => self.stack.push(&ex),
//             Expr::Literal(_) | Expr::Name(_) | Expr::Path(_) | Expr::Range(_) | Expr::Type(_) => (),
//         }
//     }
// }

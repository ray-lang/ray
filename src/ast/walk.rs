use crate::ast::{
    BinOp, Cast, Curly, CurlyElement, Decl, Dot, Expr, Index, List, Module, Name, New, Node,
    Pattern, Range, Tuple, UnaryOp,
    expr::{Assign, Block, Call, Closure, For, Func, If, Loop, Sequence, While},
};

#[derive(Clone, Copy)]
pub enum WalkItem<'a> {
    Module(&'a Module<(), Decl>),
    Decl(&'a Node<Decl>),
    Expr(&'a Node<Expr>),
    Func(&'a Node<Func>),
    Pattern(&'a Node<Pattern>),
    Name(&'a Node<Name>),
    CurlyElement(&'a Node<CurlyElement>),
}

pub struct ModuleWalk<'a> {
    stack: Vec<WalkItem<'a>>,
}

impl<'a> Iterator for ModuleWalk<'a> {
    type Item = WalkItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;

        match node {
            WalkItem::Module(module) => {
                for decl in module.decls.iter().rev() {
                    self.stack.push(WalkItem::Decl(decl));
                }
            }
            WalkItem::Decl(decl) => match &decl.value {
                Decl::Func(func) => push_func(self, func),
                Decl::Trait(tr) => {
                    for field in tr.fields.iter().rev() {
                        self.stack.push(WalkItem::Decl(field));
                    }
                }
                Decl::Impl(imp) => {
                    if let Some(funcs) = imp.funcs.as_ref() {
                        for func in funcs.iter().rev() {
                            self.stack.push(WalkItem::Func(func));
                        }
                    }
                }
                Decl::Extern(ext) => {
                    self.stack.push(WalkItem::Decl(ext.decl_node()));
                }
                Decl::Mutable(_)
                | Decl::Name(_)
                | Decl::Struct(_)
                | Decl::Declare(_)
                | Decl::FnSig(_)
                | Decl::TypeAlias(_, _) => {}
            },
            WalkItem::Func(func) => push_func(self, func),
            WalkItem::Expr(expr) => match &expr.value {
                Expr::Assign(assign) => push_assign(self, assign),
                Expr::Block(block) => push_block(self, block),
                Expr::Boxed(boxed) => self.stack.push(WalkItem::Expr(&boxed.inner)),
                Expr::Call(call) => push_call(self, call),
                Expr::Closure(closure) => push_closure(self, closure),
                Expr::Deref(deref) => self.stack.push(WalkItem::Expr(&deref.expr)),
                Expr::Func(func) => push_func(self, func),
                Expr::For(for_expr) => push_for(self, for_expr),
                Expr::If(if_expr) => push_if(self, if_expr),
                Expr::Loop(loop_expr) => push_loop(self, loop_expr),
                Expr::Pattern(pattern) => push_pattern(self, pattern),
                Expr::Sequence(sequence) => push_sequence(self, sequence),
                Expr::While(while_expr) => push_while(self, while_expr),
                Expr::BinOp(bin_op) => push_bin_op(self, bin_op),
                Expr::Cast(cast) => push_cast(self, cast),
                Expr::Curly(curly) => push_curly(self, curly),
                Expr::Dot(dot) => push_dot(self, dot),
                Expr::Index(index) => push_index(self, index),
                Expr::List(list) => push_list(self, list),
                Expr::New(new) => push_new(self, new),
                Expr::Range(range) => push_range(self, range),
                Expr::Ref(rf) => self.stack.push(WalkItem::Expr(&rf.expr)),
                Expr::Tuple(tuple) => push_tuple(self, tuple),
                Expr::UnaryOp(unary) => push_unary_op(self, unary),

                Expr::Return(maybe_node) | Expr::Break(maybe_node) => {
                    if let Some(node) = maybe_node {
                        self.stack.push(WalkItem::Expr(&node));
                    }
                }

                Expr::DefaultValue(node)
                | Expr::Labeled(_, node)
                | Expr::Paren(node)
                | Expr::TypeAnnotated(node, _)
                | Expr::Unsafe(node) => self.stack.push(WalkItem::Expr(&node)),

                // ignore "atoms"
                Expr::Asm(_)
                | Expr::Literal(_)
                | Expr::Missing(_)
                | Expr::Name(_)
                | Expr::Path(_)
                | Expr::Type(_) => {}
            },
            WalkItem::Pattern(pattern) => push_pattern(self, pattern),
            WalkItem::CurlyElement(element) => push_curly_element(self, element),
            WalkItem::Name(_) => {}
        }

        Some(node)
    }
}

pub fn walk_module(module: &Module<(), Decl>) -> ModuleWalk<'_> {
    ModuleWalk {
        stack: vec![WalkItem::Module(module)],
    }
}

fn push_assign<'a>(walk: &mut ModuleWalk<'a>, assign: &'a Assign) {
    walk.stack.push(WalkItem::Pattern(&assign.lhs));
    walk.stack.push(WalkItem::Expr(assign.rhs.as_ref()));
}

fn push_block<'a>(walk: &mut ModuleWalk<'a>, block: &'a Block) {
    for stmt in block.stmts.iter().rev() {
        walk.stack.push(WalkItem::Expr(stmt));
    }
}

fn push_call<'a>(walk: &mut ModuleWalk<'a>, call: &'a Call) {
    walk.stack.push(WalkItem::Expr(call.callee.as_ref()));
    for arg in call.args.items.iter().rev() {
        walk.stack.push(WalkItem::Expr(arg));
    }
}

fn push_closure<'a>(walk: &mut ModuleWalk<'a>, closure: &'a Closure) {
    walk.stack.push(WalkItem::Expr(closure.body.as_ref()));
    for arg in closure.args.items.iter().rev() {
        walk.stack.push(WalkItem::Expr(arg));
    }
}

fn push_func<'a>(walk: &mut ModuleWalk<'a>, func: &'a Func) {
    if let Some(body) = func.body.as_ref() {
        walk.stack.push(WalkItem::Expr(body));
    }
}

fn push_for<'a>(walk: &mut ModuleWalk<'a>, for_expr: &'a For) {
    walk.stack.push(WalkItem::Pattern(&for_expr.pat));
    walk.stack.push(WalkItem::Expr(for_expr.body.as_ref()));
    walk.stack.push(WalkItem::Expr(for_expr.expr.as_ref()));
}

fn push_if<'a>(walk: &mut ModuleWalk<'a>, if_expr: &'a If) {
    if let Some(els) = if_expr.els.as_ref() {
        walk.stack.push(WalkItem::Expr(els));
    }
    walk.stack.push(WalkItem::Expr(if_expr.then.as_ref()));
    walk.stack.push(WalkItem::Expr(if_expr.cond.as_ref()));
}

fn push_loop<'a>(walk: &mut ModuleWalk<'a>, loop_expr: &'a Loop) {
    walk.stack.push(WalkItem::Expr(loop_expr.body.as_ref()));
}

fn push_sequence<'a>(walk: &mut ModuleWalk<'a>, sequence: &'a Sequence) {
    for item in sequence.items.iter().rev() {
        walk.stack.push(WalkItem::Expr(item));
    }
}

fn push_while<'a>(walk: &mut ModuleWalk<'a>, while_expr: &'a While) {
    walk.stack.push(WalkItem::Expr(while_expr.body.as_ref()));
    walk.stack.push(WalkItem::Expr(while_expr.cond.as_ref()));
}

fn push_pattern<'a>(walk: &mut ModuleWalk<'a>, pattern: &'a Pattern) {
    match pattern {
        Pattern::Sequence(seq) | Pattern::Tuple(seq) => {
            for pat in seq.iter().rev() {
                walk.stack.push(WalkItem::Pattern(pat));
            }
        }
        Pattern::Deref(name) => {
            walk.stack.push(WalkItem::Name(name));
        }
        Pattern::Name(_) | Pattern::Missing(_) => {}
    }
}

fn push_bin_op<'a>(walk: &mut ModuleWalk<'a>, bin_op: &'a BinOp) {
    walk.stack.push(WalkItem::Expr(&bin_op.rhs));
    walk.stack.push(WalkItem::Expr(&bin_op.lhs));
}

fn push_cast<'a>(walk: &mut ModuleWalk<'a>, cast: &'a Cast) {
    walk.stack.push(WalkItem::Expr(&cast.lhs));
}

fn push_curly<'a>(walk: &mut ModuleWalk<'a>, curly: &'a Curly) {
    for elem in curly.elements.iter().rev() {
        walk.stack.push(WalkItem::CurlyElement(elem));
    }
}

fn push_curly_element<'a>(walk: &mut ModuleWalk<'a>, element: &'a CurlyElement) {
    match element {
        CurlyElement::Name(_) => {}
        CurlyElement::Labeled(_, node) => {
            walk.stack.push(WalkItem::Expr(node));
        }
    }
}

fn push_dot<'a>(walk: &mut ModuleWalk<'a>, dot: &'a Dot) {
    walk.stack.push(WalkItem::Name(&dot.rhs));
    walk.stack.push(WalkItem::Expr(&dot.lhs));
}

fn push_index<'a>(walk: &mut ModuleWalk<'a>, index: &'a Index) {
    walk.stack.push(WalkItem::Expr(&index.index));
    walk.stack.push(WalkItem::Expr(&index.lhs));
}

fn push_list<'a>(walk: &mut ModuleWalk<'a>, list: &'a List) {
    for elem in list.items.iter().rev() {
        walk.stack.push(WalkItem::Expr(elem));
    }
}

fn push_new<'a>(walk: &mut ModuleWalk<'a>, new: &'a New) {
    if let Some(count) = &new.count {
        walk.stack.push(WalkItem::Expr(&count));
    }
}

fn push_range<'a>(walk: &mut ModuleWalk<'a>, range: &'a Range) {
    walk.stack.push(WalkItem::Expr(&range.end));
    walk.stack.push(WalkItem::Expr(&range.start));
}

fn push_tuple<'a>(walk: &mut ModuleWalk<'a>, tuple: &'a Tuple) {
    for elem in tuple.seq.items.iter().rev() {
        walk.stack.push(WalkItem::Expr(elem));
    }
}

fn push_unary_op<'a>(walk: &mut ModuleWalk<'a>, unary_op: &'a UnaryOp) {
    walk.stack.push(WalkItem::Expr(&unary_op.expr));
}

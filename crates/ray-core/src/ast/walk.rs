use crate::ast::{
    BinOp, Cast, Curly, CurlyElement, Decl, Dot, Expr, Index, List, Module, Name, New, Node,
    Pattern, Range, Tuple, UnaryOp,
    expr::{Assign, Block, Call, Closure, For, Func, If, Loop, Sequence, While},
};

#[derive(Debug, Clone, Copy)]
pub enum WalkItem<'a> {
    Module(&'a Module<(), Decl>),
    Decl(&'a Node<Decl>),
    Expr(&'a Node<Expr>),
    Func(&'a Node<Func>),
    Pattern(&'a Node<Pattern>),
    Name(&'a Node<Name>),
    CurlyElement(&'a Node<CurlyElement>),
    EnterScope(WalkScopeKind),
    ExitScope(WalkScopeKind),
}

#[derive(Debug, Clone, Copy)]
pub enum WalkScopeKind {
    Module,
    Function,
    Block,
    Closure,
}

pub struct ModuleWalk<'a> {
    stack: Vec<StackEntry<'a>>,
}

#[derive(Debug, Clone, Copy)]
enum StackEntry<'a> {
    EnterNode(WalkItem<'a>),
    VisitNode(WalkItem<'a>),
    ExitScope(WalkScopeKind),
}

impl<'a> Iterator for ModuleWalk<'a> {
    type Item = WalkItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(entry) = self.stack.pop() {
            match entry {
                StackEntry::ExitScope(kind) => return Some(WalkItem::ExitScope(kind)),
                StackEntry::VisitNode(item) => return Some(item),
                StackEntry::EnterNode(item) => {
                    if let Some(kind) = scope_kind(&item) {
                        self.stack.push(StackEntry::ExitScope(kind));
                        push_children(self, &item);
                        self.stack.push(StackEntry::VisitNode(item));
                        return Some(WalkItem::EnterScope(kind));
                    } else {
                        push_children(self, &item);
                        self.stack.push(StackEntry::VisitNode(item));
                        continue;
                    }
                }
            }
        }

        None
    }
}

pub fn walk_module(module: &Module<(), Decl>) -> ModuleWalk<'_> {
    ModuleWalk {
        stack: vec![StackEntry::EnterNode(WalkItem::Module(module))],
    }
}

fn push_children<'a>(walk: &mut ModuleWalk<'a>, item: &WalkItem<'a>) {
    match item {
        WalkItem::Module(module) => {
            for decl in module.decls.iter().rev() {
                walk.stack.push(StackEntry::EnterNode(WalkItem::Decl(decl)));
            }
        }
        WalkItem::Decl(decl) => match &decl.value {
            Decl::Func(func) => push_func(walk, func),
            Decl::Trait(tr) => {
                for field in tr.fields.iter().rev() {
                    walk.stack.push(StackEntry::EnterNode(WalkItem::Decl(field)));
                }
            }
            Decl::Impl(imp) => {
                if let Some(funcs) = imp.funcs.as_ref() {
                    for func in funcs.iter().rev() {
                        walk.stack.push(StackEntry::EnterNode(WalkItem::Func(func)));
                    }
                }
            }
            Decl::Extern(ext) => {
                walk.stack
                    .push(StackEntry::EnterNode(WalkItem::Decl(ext.decl_node())));
            }
            Decl::Mutable(_)
            | Decl::Name(_)
            | Decl::Struct(_)
            | Decl::Declare(_)
            | Decl::FnSig(_)
            | Decl::TypeAlias(_, _) => {}
        },
        WalkItem::Func(func) => push_func(walk, func),
        WalkItem::Expr(expr) => match &expr.value {
            Expr::Assign(assign) => push_assign(walk, assign),
            Expr::Block(block) => push_block(walk, block),
            Expr::Boxed(boxed) => {
                walk.stack.push(StackEntry::EnterNode(WalkItem::Expr(&boxed.inner)))
            }
            Expr::Call(call) => push_call(walk, call),
            Expr::Closure(closure) => push_closure(walk, closure),
            Expr::Deref(deref) => {
                walk.stack.push(StackEntry::EnterNode(WalkItem::Expr(&deref.expr)))
            }
            Expr::Func(func) => push_func(walk, func),
            Expr::For(for_expr) => push_for(walk, for_expr),
            Expr::If(if_expr) => push_if(walk, if_expr),
            Expr::Loop(loop_expr) => push_loop(walk, loop_expr),
            Expr::Pattern(pattern) => push_pattern(walk, pattern),
            Expr::Sequence(sequence) => push_sequence(walk, sequence),
            Expr::While(while_expr) => push_while(walk, while_expr),
            Expr::BinOp(bin_op) => push_bin_op(walk, bin_op),
            Expr::Cast(cast) => push_cast(walk, cast),
            Expr::Curly(curly) => push_curly(walk, curly),
            Expr::Dot(dot) => push_dot(walk, dot),
            Expr::Index(index) => push_index(walk, index),
            Expr::List(list) => push_list(walk, list),
            Expr::New(new) => push_new(walk, new),
            Expr::Range(range) => push_range(walk, range),
            Expr::Ref(rf) => {
                walk.stack.push(StackEntry::EnterNode(WalkItem::Expr(&rf.expr)))
            }
            Expr::Tuple(tuple) => push_tuple(walk, tuple),
            Expr::UnaryOp(unary) => push_unary_op(walk, unary),
            Expr::Return(maybe_node) | Expr::Break(maybe_node) => {
                if let Some(node) = maybe_node {
                    walk.stack.push(StackEntry::EnterNode(WalkItem::Expr(&node)));
                }
            }
            Expr::DefaultValue(node)
            | Expr::Labeled(_, node)
            | Expr::Paren(node)
            | Expr::TypeAnnotated(node, _)
            | Expr::Unsafe(node)
            | Expr::Some(node) => {
                walk.stack.push(StackEntry::EnterNode(WalkItem::Expr(&node)))
            }
            Expr::Literal(_)
            | Expr::Missing(_)
            | Expr::Name(_)
            | Expr::Path(_)
            | Expr::Type(_) => {}
        },
        WalkItem::Pattern(pattern) => push_pattern(walk, pattern),
        WalkItem::CurlyElement(element) => push_curly_element(walk, element),
        WalkItem::Name(_) | WalkItem::EnterScope(_) | WalkItem::ExitScope(_) => {}
    }
}

fn push_assign<'a>(walk: &mut ModuleWalk<'a>, assign: &'a Assign) {
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Pattern(&assign.lhs)));
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(assign.rhs.as_ref())));
}

fn push_block<'a>(walk: &mut ModuleWalk<'a>, block: &'a Block) {
    for stmt in block.stmts.iter().rev() {
        walk.stack.push(StackEntry::EnterNode(WalkItem::Expr(stmt)));
    }
}

fn push_call<'a>(walk: &mut ModuleWalk<'a>, call: &'a Call) {
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(call.callee.as_ref())));
    for arg in call.args.items.iter().rev() {
        walk.stack.push(StackEntry::EnterNode(WalkItem::Expr(arg)));
    }
}

fn push_closure<'a>(walk: &mut ModuleWalk<'a>, closure: &'a Closure) {
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(closure.body.as_ref())));
    for arg in closure.args.items.iter().rev() {
        walk.stack.push(StackEntry::EnterNode(WalkItem::Expr(arg)));
    }
}

fn push_func<'a>(walk: &mut ModuleWalk<'a>, func: &'a Func) {
    if let Some(body) = func.body.as_ref() {
        walk.stack
            .push(StackEntry::EnterNode(WalkItem::Expr(body)));
    }
}

fn push_for<'a>(walk: &mut ModuleWalk<'a>, for_expr: &'a For) {
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Pattern(&for_expr.pat)));
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(for_expr.body.as_ref())));
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(for_expr.expr.as_ref())));
}

fn push_if<'a>(walk: &mut ModuleWalk<'a>, if_expr: &'a If) {
    if let Some(els) = if_expr.els.as_ref() {
        walk.stack
            .push(StackEntry::EnterNode(WalkItem::Expr(els)));
    }
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(if_expr.then.as_ref())));
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(if_expr.cond.as_ref())));
}

fn push_loop<'a>(walk: &mut ModuleWalk<'a>, loop_expr: &'a Loop) {
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(loop_expr.body.as_ref())));
}

fn push_sequence<'a>(walk: &mut ModuleWalk<'a>, sequence: &'a Sequence) {
    for item in sequence.items.iter().rev() {
        walk.stack.push(StackEntry::EnterNode(WalkItem::Expr(item)));
    }
}

fn push_while<'a>(walk: &mut ModuleWalk<'a>, while_expr: &'a While) {
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(while_expr.body.as_ref())));
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(while_expr.cond.as_ref())));
}

fn push_pattern<'a>(walk: &mut ModuleWalk<'a>, pattern: &'a Pattern) {
    match pattern {
        Pattern::Sequence(seq) | Pattern::Tuple(seq) => {
            for pat in seq.iter().rev() {
                walk.stack.push(StackEntry::EnterNode(WalkItem::Pattern(pat)));
            }
        }
        Pattern::Deref(name) => {
            walk.stack.push(StackEntry::EnterNode(WalkItem::Name(name)));
        }
        Pattern::Dot(lhs, rhs) => {
            walk.stack.push(StackEntry::EnterNode(WalkItem::Name(rhs)));
            walk.stack
                .push(StackEntry::EnterNode(WalkItem::Pattern(lhs)));
        }
        Pattern::Some(pattern) => {
            walk.stack
                .push(StackEntry::EnterNode(WalkItem::Pattern(pattern)));
        }
        Pattern::Name(_) | Pattern::Missing(_) => {}
    }
}

fn push_bin_op<'a>(walk: &mut ModuleWalk<'a>, bin_op: &'a BinOp) {
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(&bin_op.rhs)));
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(&bin_op.lhs)));
}

fn push_cast<'a>(walk: &mut ModuleWalk<'a>, cast: &'a Cast) {
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(&cast.lhs)));
}

fn push_curly<'a>(walk: &mut ModuleWalk<'a>, curly: &'a Curly) {
    for elem in curly.elements.iter().rev() {
        walk.stack
            .push(StackEntry::EnterNode(WalkItem::CurlyElement(elem)));
    }
}

fn push_curly_element<'a>(walk: &mut ModuleWalk<'a>, element: &'a CurlyElement) {
    match element {
        CurlyElement::Name(_) => {}
        CurlyElement::Labeled(_, node) => {
            walk.stack.push(StackEntry::EnterNode(WalkItem::Expr(node)));
        }
    }
}

fn push_dot<'a>(walk: &mut ModuleWalk<'a>, dot: &'a Dot) {
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Name(&dot.rhs)));
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(&dot.lhs)));
}

fn push_index<'a>(walk: &mut ModuleWalk<'a>, index: &'a Index) {
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(&index.index)));
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(&index.lhs)));
}

fn push_list<'a>(walk: &mut ModuleWalk<'a>, list: &'a List) {
    for elem in list.items.iter().rev() {
        walk.stack.push(StackEntry::EnterNode(WalkItem::Expr(elem)));
    }
}

fn push_new<'a>(walk: &mut ModuleWalk<'a>, new: &'a New) {
    if let Some(count) = &new.count {
        walk.stack
            .push(StackEntry::EnterNode(WalkItem::Expr(&count)));
    }
}

fn push_range<'a>(walk: &mut ModuleWalk<'a>, range: &'a Range) {
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(&range.end)));
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(&range.start)));
}

fn push_tuple<'a>(walk: &mut ModuleWalk<'a>, tuple: &'a Tuple) {
    for elem in tuple.seq.items.iter().rev() {
        walk.stack.push(StackEntry::EnterNode(WalkItem::Expr(elem)));
    }
}

fn push_unary_op<'a>(walk: &mut ModuleWalk<'a>, unary_op: &'a UnaryOp) {
    walk.stack
        .push(StackEntry::EnterNode(WalkItem::Expr(&unary_op.expr)));
}

fn scope_kind<'a>(item: &WalkItem<'a>) -> Option<WalkScopeKind> {
    match item {
        WalkItem::Decl(decl) => match &decl.value {
            Decl::Func(func) if func.body.is_some() => Some(WalkScopeKind::Function),
            _ => None,
        },
        WalkItem::Func(func) if func.body.is_some() => Some(WalkScopeKind::Function),
        WalkItem::Expr(expr) => match &expr.value {
            Expr::Block(_) => Some(WalkScopeKind::Block),
            Expr::Closure(_) => Some(WalkScopeKind::Closure),
            Expr::Func(func) if func.body.is_some() => Some(WalkScopeKind::Function),
            Expr::For(_) => Some(WalkScopeKind::Block),
            _ => None,
        },
        _ => None,
    }
}

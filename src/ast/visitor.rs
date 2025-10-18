use super::{Decl, Expr, Module};

pub struct Visitor<'a, Ctx> {
    ctx: &'a mut Ctx,
}

impl<'a, Ctx> Visitor<'a, Ctx> {
    pub fn visit<T>(&mut self, module: &mut Module<Expr, Decl>) -> T {
        todo!()
    }

    fn visit_expr<T>(&mut self, expr: &mut Expr) -> T {
        match expr {
            Expr::Assign(_) => todo!(),
            Expr::Asm(_) => todo!(),
            Expr::BinOp(_) => todo!(),
            Expr::Block(_) => todo!(),
            Expr::Break(_) => todo!(),
            Expr::Call(_) => todo!(),
            Expr::Cast(_) => todo!(),
            Expr::Closure(_) => todo!(),
            Expr::Curly(_) => todo!(),
            Expr::DefaultValue(_) => todo!(),
            Expr::Dot(_) => todo!(),
            Expr::Func(_) => todo!(),
            Expr::For(_) => todo!(),
            Expr::If(_) => todo!(),
            Expr::Index(_) => todo!(),
            Expr::Labeled(_, _) => todo!(),
            Expr::List(_) => todo!(),
            Expr::Literal(_) => todo!(),
            Expr::Loop(_) => todo!(),
            Expr::Name(_) => todo!(),
            Expr::New(_) => todo!(),
            Expr::Path(_) => todo!(),
            Expr::Pattern(_) => todo!(),
            Expr::Paren(_) => todo!(),
            Expr::Range(_) => todo!(),
            Expr::Return(_) => todo!(),
            Expr::Sequence(_) => todo!(),
            Expr::Tuple(_) => todo!(),
            Expr::Type(_) => todo!(),
            Expr::TypeAnnotated(_, _) => todo!(),
            Expr::UnaryOp(_) => todo!(),
            Expr::Unsafe(_) => todo!(),
            Expr::While(_) => todo!(),
            Expr::Missing(_) => todo!(),
        }
    }
}

// pub trait Visitable {
//     type T;

//     fn visit(&mut self) -> Self::T;
// }

// impl Visitable for Module<(), Decl> {
//     type T = ;

//     fn visit(&mut self) -> Self::T {
//         todo!()
//     }
// }

// impl CollectConstraints for Module<(), Decl>
// impl CollectDeclarations for Node<Decl>
// impl CollectDeclarations for (&ast::Fn, &Source, Option<&Ty>)
// impl CollectConstraints for (&Box<T>, &Source)
// impl CollectConstraints for Node<Expr>
// impl CollectConstraints for (&Asm, &Source)
// impl CollectConstraints for (&BinOp, &Source)
// impl CollectConstraints for (&Block, &Source)
// impl CollectConstraints for (&Call, &Source)
// impl CollectConstraints for (&Cast, &Source)
// impl CollectConstraints for (&Curly, &Source)
// impl CollectConstraints for (&Dot, &Source)
// impl CollectConstraints for (&ast::Fn, &Source)
// impl CollectConstraints for (&For, &Source)
// impl CollectConstraints for (&If, &Source)
// impl CollectConstraints for (&List, &Source)
// impl CollectConstraints for (&Literal, &Source)
// impl CollectConstraints for (&Name, &Source)
// impl CollectConstraints for (&New, &Source)
// impl CollectConstraints for (&Pattern, &Source)
// impl CollectConstraints for (&Path, &Source)
// impl CollectConstraints for (&Range, &Source)
// impl CollectConstraints for (&Tuple, &Source)
// impl CollectConstraints for (&UnaryOp, &Source)
// impl CollectConstraints for (&While, &Source)

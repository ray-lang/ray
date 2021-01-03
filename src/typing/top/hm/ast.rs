pub enum LitKind {
    Int,
    Float,
    String,
    Char,
}

pub enum Expr {
    Var(String),
    Lit(LitKind),
    App(Box<Expr>, Vec<Expr>),
    Abs(Vec<String>, Box<Expr>),
    Cond(Box<Expr>, Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
}

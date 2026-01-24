use crate::{pathlib::Path, ty::Ty};

pub struct TyParser<'a> {
    src: &'a str,
    index: usize,
}

impl<'a> TyParser<'a> {
    pub fn new(src: &'a str) -> TyParser<'a> {
        Self { src, index: 0 }
    }

    pub fn parse(src: &'a str) -> Result<Ty, String> {
        let mut p = TyParser::new(src);
        p.parse_ty()
    }

    pub fn peek(&mut self) -> Option<char> {
        self.consume_whitespace();
        self.src.chars().nth(self.index)
    }

    fn peek_n(&mut self, count: usize) -> Option<&str> {
        self.consume_whitespace();
        self.src.get(self.index..self.index + count)
    }

    pub fn next(&mut self) -> Option<char> {
        self.consume_whitespace();
        let ch = self.src.chars().nth(self.index);
        self.index += 1;
        ch
    }

    fn next_n(&mut self, count: usize) -> Option<&str> {
        self.consume_whitespace();
        let s = self.src.get(self.index..self.index + count);
        self.index += count;
        s
    }

    pub fn expect(&mut self, s: &str) -> Option<&str> {
        self.consume_whitespace();
        if let Some(next) = self.next_n(s.len()) {
            if next != s {
                panic!("expected `{}`, found `{}`", s, next)
            }
            return Some(next);
        }

        panic!("expected `{}`, found end of input", s)
    }

    fn advance(&mut self, count: usize) {
        self.index += count;
    }

    fn consume_whitespace(&mut self) {
        while let Some(ch) = self.src.chars().nth(self.index) {
            if !ch.is_whitespace() {
                break;
            }

            self.index += 1;
        }
    }

    pub fn parse_id(&mut self) -> String {
        let mut s = String::new();
        while matches!(self.peek(), Some(p) if p.is_ascii_alphanumeric() || p == '_') {
            let Some(ch) = self.next() else {
                break;
            };

            s.push(ch);
        }
        s
    }

    pub fn parse_num(&mut self) -> usize {
        let mut s = String::new();
        while matches!(self.peek(), Some(p) if p.is_numeric()) {
            let Some(ch) = self.next() else {
                break;
            };

            s.push(ch);
        }
        s.parse().unwrap()
    }

    fn path_with(&mut self, first: String) -> Path {
        let mut parts = vec![first];
        while let Some("::") = self.peek_n(2) {
            self.advance(2);

            let id = self.parse_id();
            if id.is_empty() {
                break;
            }
            parts.push(id);
        }
        Path::from(parts)
    }

    pub fn parse_ty(&mut self) -> Result<Ty, String> {
        self.parse_ty_base(None)
    }

    fn parse_ty_params(&mut self) -> Result<Option<Vec<Ty>>, String> {
        let Some('[') = self.peek() else {
            return Ok(None);
        };

        self.expect("[");
        let mut tys = vec![];
        loop {
            let ty = self.parse_ty()?;
            tys.push(ty);
            if let Some(']') = self.peek() {
                break;
            }
            self.expect(",");
        }

        self.expect("]");

        Ok(Some(tys))
    }

    fn parse_ty_complex(&mut self) -> Result<Option<Ty>, String> {
        Ok(if let Some('*') = self.peek() {
            Some(self.parse_ptr_ty()?)
        } else if let Some("Fn") = self.peek_n(2) {
            Some(self.parse_fn_ty()?)
        } else if let Some('[') = self.peek() {
            Some(self.parse_arr_ty()?)
        } else if let Some('\'') = self.peek() {
            Some(self.parse_generic_ty()?)
        } else if let Some('?') = self.peek() {
            Some(self.parse_ty_var()?)
        } else if let Some('(') = self.peek() {
            Some(self.parse_tuple_ty()?)
        } else {
            None
        })
    }

    fn parse_ty_base(&mut self, ident: Option<String>) -> Result<Ty, String> {
        if let Some(t) = self.parse_ty_complex()? {
            Ok(t)
        } else {
            let name = if let Some(name) = ident {
                name
            } else {
                self.parse_id()
            };

            let path = if let Some("::") = self.peek_n(2) {
                self.path_with(name)
            } else {
                Path::from(vec![name])
            };

            self.parse_ty_with_path(path)
        }
    }

    fn parse_ptr_ty(&mut self) -> Result<Ty, String> {
        self.expect("*");
        let ptee_ty = self.parse_ty()?;
        Ok(Ty::ref_of(ptee_ty))
    }

    fn parse_arr_ty(&mut self) -> Result<Ty, String> {
        self.expect("[");
        let el_ty = self.parse_ty()?;
        self.expect(";");
        let size = self.parse_arr_ty_size()?;
        self.expect("]");
        Ok(Ty::array(el_ty, size))
    }

    fn parse_arr_ty_size(&mut self) -> Result<usize, String> {
        let mut size_str = String::new();
        while matches!(self.peek(), Some(ch) if ch.is_numeric()) {
            let Some(ch) = self.next() else { break };
            size_str.push(ch);
        }

        size_str
            .parse::<usize>()
            .map_err(|e| format!("`{}` is an invalid size: {}", size_str, e))
    }

    fn parse_generic_ty(&mut self) -> Result<Ty, String> {
        self.expect("'");
        let name = self.parse_id();
        let path = Path::from(vec![name]);
        Ok(Ty::var(path))
    }

    fn parse_ty_var(&mut self) -> Result<Ty, String> {
        self.expect("?");
        let mut name = "?".to_string();
        name.push_str(&self.parse_id());
        let path = Path::from(vec![name]);
        Ok(Ty::var(path))
    }

    fn parse_ty_with_path(&mut self, path: Path) -> Result<Ty, String> {
        let ty_params = self.parse_ty_params()?;

        let builtin_name = if path.len() == 1 {
            Some(path.as_str())
        } else {
            None
        };

        let ty = if let Some(mut ty) = builtin_name.and_then(Ty::from_str) {
            match &mut ty {
                Ty::Proj(_, el_tys) => {
                    if let Some(ty_params) = ty_params {
                        *el_tys = ty_params;
                    }
                }
                Ty::RawPtr(ty) => {
                    let count = if let Some(mut ty_params) = ty_params {
                        if ty_params.len() == 0 {
                            0
                        } else {
                            let count = ty_params.len();
                            let ty_param = ty_params.remove(0);
                            *(ty.as_mut()) = ty_param;
                            count
                        }
                    } else {
                        0
                    };

                    if count != 1 {
                        return Err(format!(
                            "rawptr expected one type parameter, but found {}",
                            count
                        ));
                    }
                }
                _ => {}
            }
            ty
        } else {
            Ty::with_tys(path, ty_params.unwrap_or_default())
        };

        Ok(ty)
    }

    fn parse_fn_ty(&mut self) -> Result<Ty, String> {
        // Fn(<params>) -> <ret_ty>
        self.expect("Fn");
        let params_ty = self.parse_tuple_ty()?;
        let ret_ty = Box::new(if let Some("->") = self.peek_n(2) {
            self.advance(2);
            self.parse_ty()?
        } else {
            Ty::unit()
        });

        let param_tys = match params_ty {
            Ty::Tuple(tys) => tys,
            ty => vec![ty],
        };
        let fn_ty = Ty::Func(param_tys, ret_ty);
        Ok(fn_ty)
    }

    pub fn parse_tuple_ty(&mut self) -> Result<Ty, String> {
        let mut tys = vec![];
        self.expect("(");

        loop {
            if let Some(')') = self.peek() {
                break;
            }

            let ty = self.parse_ty()?;
            tys.push(ty);

            if let Some(')') = self.peek() {
                break;
            }

            self.expect(",");
        }

        self.expect(")");
        Ok(Ty::tuple(tys))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        pathlib::Path,
        ty::{Ty, parser::TyParser},
    };

    #[test]
    fn parses_basic_ty() {
        let ty = TyParser::parse("int").expect("could not parse `int`");
        assert_eq!(ty, Ty::int());
        let ty = TyParser::parse("string").expect("could not parse `string`");
        assert_eq!(ty, Ty::string());
        let ty = TyParser::parse("i32").expect("could not parse `i32`");
        assert_eq!(ty, Ty::i32());
    }

    #[test]
    fn parses_path_ty() {
        let ty = TyParser::parse("pkg::T").expect("could not parse `pkg::T`");
        let mut path = Path::new();
        path.append_mut("pkg").append_mut("T");
        assert_eq!(ty, Ty::Const(path.into()));

        let ty = TyParser::parse("pkg::mod::T").expect("could not parse `pkg::mod::T`");
        let mut path = Path::new();
        path.append_mut("pkg").append_mut("mod").append_mut("T");
        assert_eq!(ty, Ty::Const(path.into()));
    }

    #[test]
    fn parses_ptr_ty() {
        let ty = TyParser::parse("*T").expect("could not parse `*T`");
        let mut path = Path::new();
        path.append_mut("T");
        assert_eq!(ty, Ty::ref_of(Ty::Const(path.into())));

        let ty = TyParser::parse("*pkg::T").expect("could not parse `*pkg::T`");
        let mut path = Path::new();
        path.append_mut("pkg").append_mut("T");
        assert_eq!(ty, Ty::ref_of(Ty::Const(path.into())));
    }

    #[test]
    fn parses_tuple_ty() {
        let ty = TyParser::parse("()").expect("could not parse `()`");
        assert_eq!(ty, Ty::unit());

        let ty = TyParser::parse("(T)").expect("could not parse `(T)`");
        assert_eq!(ty, Ty::tuple(vec![Ty::con("T")]));

        let ty = TyParser::parse("(A, B)").expect("could not parse `(A, B)`");
        assert_eq!(ty, Ty::tuple(vec![Ty::con("A"), Ty::con("B")]));
    }

    #[test]
    fn parses_array_ty() {
        let ty = TyParser::parse("[u32; 10]").expect("could not parse `[u32; 10]`");
        assert_eq!(ty, Ty::array(Ty::u32(), 10));

        let ty = TyParser::parse("[(u32, u32); 10]").expect("could not parse `[(u32, u32); 10]`");
        assert_eq!(ty, Ty::array(Ty::tuple(vec![Ty::u32(), Ty::u32()]), 10));

        let ty =
            TyParser::parse("(i8, [(u32, u32); 10], string)").expect("could not parse `[u32; 10]`");
        assert_eq!(
            ty,
            Ty::tuple(vec![
                Ty::i8(),
                Ty::array(Ty::tuple(vec![Ty::u32(), Ty::u32()]), 10),
                Ty::string()
            ])
        );
    }

    #[test]
    fn parses_ty_with_params() {
        let ty = TyParser::parse("list[T]").expect("could not parse `list[T]`");
        assert_eq!(ty, Ty::proj("list", vec![Ty::con("T")]));

        let ty = TyParser::parse("dict[K, V]").expect("could not parse `dict[K, V]`");
        assert_eq!(ty, Ty::proj("dict", vec![Ty::con("K"), Ty::con("V")]));

        let ty = TyParser::parse("pkg::A[T, U, V]").expect("could not parse `pkg::A[T, U, V]`");
        assert_eq!(
            ty,
            Ty::proj("pkg::A", vec![Ty::con("T"), Ty::con("U"), Ty::con("V")])
        );
    }

    #[test]
    fn parses_ty_nested() {
        let ty = TyParser::parse("core::dict[K, (pkg::T, U)]")
            .expect("could not parse `core::dict[K, (pkg::T, U)]`");
        assert_eq!(
            ty,
            Ty::proj(
                "core::dict",
                vec![
                    Ty::con("K"),
                    Ty::tuple(vec![Ty::con("pkg::T"), Ty::con("U")])
                ]
            )
        );
    }

    #[test]
    fn parses_fn_ty() {
        let ty = TyParser::parse("Fn(i32, uint) -> string")
            .expect("could not parse `Fn(i32, uint) -> string`");
        assert_eq!(ty, Ty::func(vec![Ty::i32(), Ty::uint()], Ty::string()));

        let ty = TyParser::parse("pkg::T[uint, Fn(i8, (u64, i64)) -> string]")
            .expect("could not parse `pkg::T[uint, Fn(i8, (u64, i64)) -> string]`");
        assert_eq!(
            ty,
            Ty::proj(
                "pkg::T",
                vec![
                    Ty::uint(),
                    Ty::func(
                        vec![Ty::i8(), Ty::tuple(vec![Ty::u64(), Ty::i64()])],
                        Ty::string()
                    )
                ]
            )
        );
    }

    #[test]
    fn parses_tys_within_delimiters() {
        let mut parser = TyParser::new("<(A, (B, C)):R>");
        parser.expect("<");
        let ty = parser
            .parse_ty()
            .expect("could not parse `(A, (B, C))` after `<`");
        assert_eq!(
            ty,
            Ty::tuple(vec![
                Ty::con("A"),
                Ty::tuple(vec![Ty::con("B"), Ty::con("C")])
            ])
        );
        parser.expect(":");
        let ty = parser.parse_ty().expect("could not parse `R` after `:`");
        assert_eq!(ty, Ty::con("R"));
        parser.expect(">");

        assert!(parser.next().is_none());
    }
}

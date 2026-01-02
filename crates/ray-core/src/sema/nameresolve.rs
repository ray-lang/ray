use std::{collections::HashMap, ops::DerefMut};

use ray_shared::{
    collections::{namecontext::NameContext, nametree::Scope},
    pathlib::Path,
    span::{Sourced, parsed::Parsed},
    ty::Ty,
};
use ray_typing::types::TyScheme;

use crate::{
    ast::{
        Assign, BinOp, Block, Boxed, Call, Cast, Closure, Curly, CurlyElement, Decl, Deref, Dict,
        Dot, Expr, Extern, FnParam, For, Func, FuncSig, If, Impl, Index, List, Literal, Loop,
        Module, Name, New, Node, Pattern, Range, Ref, ScopedAccess, Sequence, Set, Struct, Trait,
        Tuple, UnaryOp, While,
    },
    errors::{RayError, RayErrorKind, RayResult},
    sourcemap::SourceMap,
};

pub struct ResolveContext<'a> {
    ncx: &'a mut NameContext,
    srcmap: &'a mut SourceMap,
    scope_map: &'a HashMap<Path, Vec<Scope>>,
    scope_stack: Vec<Path>,
}

impl<'a> ResolveContext<'a> {
    pub fn new(
        ncx: &'a mut NameContext,
        srcmap: &'a mut SourceMap,
        scope_map: &'a HashMap<Path, Vec<Scope>>,
    ) -> Self {
        Self {
            ncx,
            srcmap,
            scope_map,
            scope_stack: Vec::new(),
        }
    }

    pub fn add_path(&mut self, path: &Path) {
        let fqn = path.to_name_vec();
        log::debug!("add_path: {:?}", fqn);
        self.ncx.nametree_mut().add_full_name(&fqn);
    }

    fn bind_local_name(&mut self, scope: &Path, name: &mut Path) {
        let full_path = scope.with_names_only().append_path(name.clone());
        log::debug!(
            "bind_local_name: scope={:?} name={} full_path={}",
            scope,
            name,
            full_path
        );
        *name = full_path.clone();
        self.add_path(&full_path);
    }

    fn push_scope_path(&mut self, scope: Path) {
        self.scope_stack.push(scope);
    }

    fn pop_scope_path(&mut self) {
        self.scope_stack.pop();
    }

    fn current_scope_or(&self, fallback: &Path) -> Path {
        self.scope_stack
            .last()
            .cloned()
            .unwrap_or_else(|| fallback.clone())
    }

    pub fn resolve_func_body(&mut self, func: &mut Func) -> RayResult<()> {
        if let Some(body) = &mut func.body {
            self.push_scope_path(func.sig.path.value.with_names_only());
            for param in &mut func.sig.params {
                self.bind_local_name(&func.sig.path, param.name_mut());
            }

            body.resolve_names(self)?;
            self.pop_scope_path();
        }
        Ok(())
    }
}

pub trait NameResolve {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()>;
}

impl NameResolve for Sourced<'_, Name> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let src = self.src();
        let name = self.path.to_string();
        let mut scopes = ctx.scope_map.get(self.src_module()).unwrap().clone();
        for scope_path in ctx.scope_stack.iter() {
            scopes.push(Scope::from(scope_path.clone()));
        }
        if ctx.scope_stack.is_empty() {
            scopes.push(Scope::from(src.path.clone()));
        }
        match ctx.ncx.resolve_name(&scopes, &name) {
            Some(fqn) => {
                log::debug!("fqn for `{}`: {}", name, fqn);
                self.path = fqn.clone();
            }
            _ => {
                log::debug!("nametree: {:#?}", ctx.ncx.nametree());
                return Err(RayError {
                    msg: format!("`{}` is undefined", self),
                    src: vec![self.src().clone()],
                    kind: RayErrorKind::Name,
                    context: Some(format!("resolving name `{self}`")),
                });
            }
        }
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Path> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let mut scopes = ctx.scope_map.get(self.src_module()).unwrap().clone();
        for scope_path in ctx.scope_stack.iter() {
            scopes.push(Scope::from(scope_path.clone()));
        }
        if ctx.scope_stack.is_empty() {
            scopes.push(Scope::from(self.src().path.clone()));
        }
        log::debug!(
            "[Path::resolve_names] looking for name `{}` in scopes: {:?}",
            self,
            scopes
        );
        match ctx.ncx.resolve_path(&scopes, &self) {
            Some(fqn) => {
                log::debug!("fqn for `{}`: {}", self, fqn);
                *self.deref_mut() = fqn.clone();
            }
            _ => {
                log::debug!("nametree: {:?}", ctx.ncx.nametree());
                return Err(RayError {
                    msg: format!("`{}` is undefined", self),
                    src: vec![self.src().clone()],
                    kind: RayErrorKind::Name,
                    context: Some(format!("resolving name from path `{self}`")),
                });
            }
        }
        Ok(())
    }
}

impl NameResolve for Node<Decl> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        match &mut self.value {
            Decl::Extern(extern_) => Sourced(extern_, &src).resolve_names(ctx),
            Decl::Mutable(_) => todo!(),
            Decl::Name(_) => todo!(),
            Decl::Declare(declare) => Sourced(declare, &src).resolve_names(ctx),
            Decl::Func(func) => Sourced(func, &src).resolve_names(ctx),
            Decl::FnSig(fnsig) => Sourced(fnsig, &src).resolve_names(ctx),
            Decl::Struct(struct_) => Sourced(struct_, &src).resolve_names(ctx),
            Decl::Trait(trait_) => Sourced(trait_, &src).resolve_names(ctx),
            Decl::TypeAlias(_, _) => todo!(),
            Decl::Impl(impl_) => Sourced(impl_, &src).resolve_names(ctx),
        }
    }
}

impl NameResolve for Node<Expr> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        Sourced(&mut self.value, &src).resolve_names(ctx)
    }
}

impl NameResolve for Node<FnParam> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        match &mut self.value {
            FnParam::Name(name) => Sourced(name, &src).resolve_names(ctx),
            FnParam::DefaultValue(param, _) => Sourced(param, &src).resolve_names(ctx),
            FnParam::Missing { .. } => Ok(()),
        }
    }
}

impl<T> NameResolve for Option<T>
where
    T: NameResolve,
{
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        if let Some(value) = self {
            value.resolve_names(ctx)
        } else {
            Ok(())
        }
    }
}

impl<T> NameResolve for Box<T>
where
    T: NameResolve,
{
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.as_mut().resolve_names(ctx)
    }
}

impl<T> NameResolve for Vec<T>
where
    T: NameResolve,
{
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        for el in self {
            el.resolve_names(ctx)?;
        }

        Ok(())
    }
}

impl NameResolve for Module<(), Decl> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        // resolve names in each declaration in the module
        self.decls.resolve_names(ctx)?;

        // resolve names the declarations again but only process the bodies of functions
        for decl in self.decls.iter_mut() {
            match decl.deref_mut() {
                Decl::Func(func) => {
                    ctx.resolve_func_body(func)?;
                }
                Decl::Impl(impl_) => {
                    if let Some(funcs) = &mut impl_.funcs {
                        for func in funcs {
                            ctx.resolve_func_body(func)?;
                        }
                    }
                }
                _ => continue,
            }
        }

        Ok(())
    }
}

impl NameResolve for Sourced<'_, Extern> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (ext, _) = self.unpack_mut();
        match ext.decl_mut() {
            Decl::Mutable(_) => todo!(),
            Decl::Name(_) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::FnSig(sig) => {
                log::debug!("NameResolve::resolve_names: extern fn sig: {:?}", sig);
                ctx.add_path(&sig.path);
            }
            _ => unreachable!(),
        }

        Ok(())
    }
}

impl NameResolve for Sourced<'_, Func> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (func, src) = self.unpack_mut();
        // note: we're only processing the signature here and not the body
        Sourced(&mut func.sig, src).resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, FuncSig> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (sig, _) = self.unpack_mut();
        ctx.add_path(&sig.path);
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Struct> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (st, _) = self.unpack_mut();
        let name = st.path.name().unwrap();
        if !Ty::is_builtin_name(&name) {
            ctx.add_path(&st.path);
        }

        Ok(())
    }
}

impl NameResolve for Sourced<'_, Trait> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (tr, src) = self.unpack_mut();
        let trait_fqn = &src.path;
        ctx.ncx
            .nametree_mut()
            .add_full_name(&trait_fqn.to_name_vec());
        log::debug!("[Trait::resolve_names] {:?}", tr);
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Impl> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (imp, src) = self.unpack_mut();
        if let Some(funcs) = &mut imp.funcs {
            for func in funcs {
                log::debug!("resolve_names: impl func: {:?}", func.sig);
                Sourced(&mut func.sig, src).resolve_names(ctx)?;
            }
        }

        Ok(())
    }
}

impl NameResolve for Sourced<'_, Expr> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (expr, src) = self.unpack_mut();
        match expr {
            Expr::Assign(a) => Sourced(a, src).resolve_names(ctx),
            Expr::BinOp(bin_op) => Sourced(bin_op, src).resolve_names(ctx),
            Expr::Block(block) => Sourced(block, src).resolve_names(ctx),
            Expr::Boxed(boxed) => Sourced(boxed, src).resolve_names(ctx),
            Expr::Break(break_) => Sourced(break_, src).resolve_names(ctx),
            Expr::Continue => Ok(()),
            Expr::Call(call) => Sourced(call, src).resolve_names(ctx),
            Expr::Cast(cast) => Sourced(cast, src).resolve_names(ctx),
            Expr::Closure(closure) => Sourced(closure, src).resolve_names(ctx),
            Expr::Curly(curly) => Sourced(curly, src).resolve_names(ctx),
            Expr::Dict(dict) => Sourced(dict, src).resolve_names(ctx),
            Expr::DefaultValue(default_value) => Sourced(default_value, src).resolve_names(ctx),
            Expr::Deref(deref) => Sourced(deref, src).resolve_names(ctx),
            Expr::Dot(dot) => Sourced(dot, src).resolve_names(ctx),
            Expr::Func(func) => Sourced(func, src).resolve_names(ctx),
            Expr::For(for_) => Sourced(for_, src).resolve_names(ctx),
            Expr::If(if_) => Sourced(if_, src).resolve_names(ctx),
            Expr::Index(index) => Sourced(index, src).resolve_names(ctx),
            Expr::Labeled(labeled, _) => Sourced(labeled, src).resolve_names(ctx),
            Expr::List(list) => Sourced(list, src).resolve_names(ctx),
            Expr::Literal(literal) => Sourced(literal, src).resolve_names(ctx),
            Expr::Loop(loop_) => Sourced(loop_, src).resolve_names(ctx),
            Expr::Name(name) => Sourced(name, src).resolve_names(ctx),
            Expr::New(new) => Sourced(new, src).resolve_names(ctx),
            Expr::Path(path) => Sourced(path, src).resolve_names(ctx),
            Expr::Pattern(pattern) => Sourced(pattern, src).resolve_names(ctx),
            Expr::Paren(paren) => Sourced(paren, src).resolve_names(ctx),
            Expr::Range(range) => Sourced(range, src).resolve_names(ctx),
            Expr::Ref(rf) => Sourced(rf, src).resolve_names(ctx),
            Expr::Return(return_) => Sourced(return_, src).resolve_names(ctx),
            Expr::Sequence(sequence) => Sourced(sequence, src).resolve_names(ctx),
            Expr::Set(set) => Sourced(set, src).resolve_names(ctx),
            Expr::ScopedAccess(scoped_access) => Sourced(scoped_access, src).resolve_names(ctx),
            Expr::Some(inner) => Sourced(inner, src).resolve_names(ctx),
            Expr::Tuple(tuple) => Sourced(tuple, src).resolve_names(ctx),
            Expr::Type(type_) => type_.resolve_names(ctx),
            Expr::TypeAnnotated(type_annotated, _) => {
                Sourced(type_annotated, src).resolve_names(ctx)
            }
            Expr::UnaryOp(unary_op) => Sourced(unary_op, src).resolve_names(ctx),
            Expr::Unsafe(unsafe_) => Sourced(unsafe_, src).resolve_names(ctx),
            Expr::While(while_) => Sourced(while_, src).resolve_names(ctx),
            Expr::Missing(_) => todo!("resolve_names: Expr::Missing: {:?}", expr),
        }
    }
}

impl NameResolve for Sourced<'_, ScopedAccess> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Assign> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (assign, src) = self.unpack_mut();
        for node in assign.lhs.paths_mut() {
            let (path, is_lvalue) = node.value;
            let base_scope = ctx.current_scope_or(&src.path.with_names_only());
            let full_path = base_scope.append_path(path.clone());
            *path = full_path.clone();

            if !is_lvalue {
                ctx.add_path(&full_path);
            }
        }

        assign.rhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, BinOp> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)?;
        self.rhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Block> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.stmts.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Boxed> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.inner.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Call> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.callee.resolve_names(ctx)?;
        self.args.items.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Cast> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Closure> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let (closure, src) = self.unpack_mut();
        let scope_suffix = format!("__closure_{:x}", closure.body.id);
        let closure_scope = src
            .path
            .with_names_only()
            .append_path(Path::from(scope_suffix));
        ctx.push_scope_path(closure_scope.clone());

        for arg in closure.args.items.iter_mut() {
            let arg_src = ctx.srcmap.get(arg);
            match &mut arg.value {
                Expr::Name(name) => {
                    ctx.bind_local_name(&closure_scope, &mut name.path);
                }
                _ => {
                    return Err(RayError {
                        msg: format!(
                            "unsupported closure parameter `{}`; only simple names are allowed",
                            arg.value
                        ),
                        src: vec![arg_src],
                        kind: RayErrorKind::Parse,
                        context: Some("resolve closure parameters".to_string()),
                    });
                }
            }
        }

        closure.body.resolve_names(ctx)?;
        ctx.pop_scope_path();
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Curly> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.elements.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Dict> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        for (key, value) in self.entries.iter_mut() {
            key.resolve_names(ctx)?;
            value.resolve_names(ctx)?;
        }
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Set> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.items.resolve_names(ctx)
    }
}

impl NameResolve for Node<CurlyElement> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        let src = ctx.srcmap.get(self);
        match &mut self.value {
            CurlyElement::Name(n) => Sourced(n, &src).resolve_names(ctx),
            CurlyElement::Labeled(_, rhs) => rhs.resolve_names(ctx),
        }
    }
}

impl NameResolve for Sourced<'_, Deref> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.expr.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Dot> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, For> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.expr.resolve_names(ctx)?;

        let scope_suffix = format!("__for_{:x}", self.body.id);
        let base_scope = ctx.current_scope_or(&self.src().path.with_names_only());
        let for_scope = base_scope.append_path(Path::from(scope_suffix));

        ctx.push_scope_path(for_scope.clone());
        for node in self.pat.paths_mut() {
            let (path, is_lvalue) = node.value;
            if is_lvalue {
                continue;
            }
            ctx.bind_local_name(&for_scope, path);
        }
        self.body.resolve_names(ctx)?;
        ctx.pop_scope_path();
        Ok(())
    }
}

impl NameResolve for Sourced<'_, If> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.cond.resolve_names(ctx)?;
        self.then.resolve_names(ctx)?;
        self.els.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Index> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.lhs.resolve_names(ctx)?;
        self.index.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, List> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.items.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Literal> {
    fn resolve_names(&mut self, _: &mut ResolveContext) -> RayResult<()> {
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Loop> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.body.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, New> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        if let Some(count) = &mut self.count {
            count.resolve_names(ctx)?
        }
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Pattern> {
    fn resolve_names(&mut self, _: &mut ResolveContext) -> RayResult<()> {
        Ok(())
    }
}

impl NameResolve for Sourced<'_, Range> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.start.resolve_names(ctx)?;
        self.end.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Ref> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.expr.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Sequence> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.items.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, Tuple> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.seq.items.resolve_names(ctx)
    }
}

impl NameResolve for Parsed<TyScheme> {
    fn resolve_names(&mut self, _: &mut ResolveContext) -> RayResult<()> {
        Ok(())
    }
}

impl NameResolve for Sourced<'_, UnaryOp> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.expr.resolve_names(ctx)
    }
}

impl NameResolve for Sourced<'_, While> {
    fn resolve_names(&mut self, ctx: &mut ResolveContext) -> RayResult<()> {
        self.cond.resolve_names(ctx)?;
        self.body.resolve_names(ctx)
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     use crate::sema::ModuleBuilder;

//     #[test]
//     fn populates_symbol_map_with_definitions_and_references() {
//         let src = r#"
// fn foo(x: int, y: int) -> int {
//     z = x + y
//     z
// }"#;

//         let result = match ModuleBuilder::from_src(src, Path::from("test")) {
//             Ok(result) => result,
//             Err(errors) => {
//                 panic!(
//                     "ModuleBuilder::build_from_src failed with errors: {:?}",
//                     errors
//                 );
//             }
//         };

//         // find definition and reference for x
//         let x_def = result.symbol_map.iter().find(|(_, target)| {
//             target.path.to_string() == "test::foo::x"
//                 && matches!(target.role, SymbolRole::Definition)
//         });
//         assert!(x_def.is_some(), "Definition for x not found");

//         let x_ref = result.symbol_map.iter().find(|(_, target)| {
//             target.path.to_string() == "test::foo::x"
//                 && matches!(target.role, SymbolRole::Reference)
//         });

//         assert!(x_ref.is_some(), "Reference for x not found");

//         // find definition and reference for z
//         let z_def = result.symbol_map.iter().find(|(_, target)| {
//             target.path.to_string() == "test::foo::z"
//                 && matches!(target.role, SymbolRole::Definition)
//         });
//         assert!(z_def.is_some(), "Definition for z not found");

//         let z_ref = result.symbol_map.iter().find(|(_, target)| {
//             target.path.to_string() == "test::foo::z"
//                 && matches!(target.role, SymbolRole::Reference)
//         });
//         assert!(z_ref.is_some(), "Reference for z not found");
//     }

//     #[test]
//     fn populates_symbol_map_with_deref_references() {
//         let src = r#"
// fn foo(ptr: *u8) {
//     *ptr = 42
// }"#;

//         let result = match ModuleBuilder::from_src(src, Path::from("test")) {
//             Ok(result) => result,
//             Err(errors) => {
//                 panic!(
//                     "ModuleBuilder::build_from_src failed with errors: {:?}",
//                     errors
//                 );
//             }
//         };

//         // find definition and reference for ptr
//         let ptr_def = result.symbol_map.iter().find(|(_, target)| {
//             target.path.to_string() == "test::foo::ptr"
//                 && matches!(target.role, SymbolRole::Definition)
//         });
//         assert!(ptr_def.is_some(), "Definition for ptr not found");

//         let ptr_ref = result.symbol_map.iter().find(|(_, target)| {
//             target.path.to_string() == "test::foo::ptr"
//                 && matches!(target.role, SymbolRole::Reference)
//         });

//         assert!(ptr_ref.is_some(), "Reference for ptr not found");
//     }

//     #[test]
//     fn populates_symbol_map_with_trait_functions() {
//         let src = r#"
// trait MyTrait['a] {
//     fn foo(self: 'a, x: int) -> int
//     fn bar(self: 'a) -> string
// }
// "#;

//         let result = match ModuleBuilder::from_src(src, Path::from("test")) {
//             Ok(result) => result,
//             Err(errors) => {
//                 panic!(
//                     "ModuleBuilder::build_from_src failed with errors: {:?}",
//                     errors
//                 );
//             }
//         };

//         println!("Symbol map: {:#?}", result.symbol_map);

//         // find trait definition
//         let trait_def = result.symbol_map.iter().find(|(_, target)| {
//             target.path.to_string() == "test::MyTrait"
//                 && matches!(target.role, SymbolRole::Definition)
//         });
//         assert!(trait_def.is_some(), "Definition for MyTrait not found");

//         // find definition for MyTrait::foo
//         let foo_def = result.symbol_map.iter().find(|(_, target)| {
//             target.path.to_string() == "test::MyTrait::foo"
//                 && matches!(target.role, SymbolRole::Definition)
//         });
//         assert!(foo_def.is_some(), "Definition for MyTrait::foo not found");

//         // find definition for MyTrait::bar
//         let bar_def = result.symbol_map.iter().find(|(_, target)| {
//             target.path.to_string() == "test::MyTrait::bar"
//                 && matches!(target.role, SymbolRole::Definition)
//         });
//         assert!(bar_def.is_some(), "Definition for MyTrait::bar not found");
//     }

//     #[test]
//     fn populates_symbol_map_with_impl_functions() {
//         let src = r#"
// trait Foo['a] {
//     fn foo(self: 'a) -> 'a
// }

// impl Foo[int] {
//     fn foo(self: int) -> int {
//         42
//     }
// }
// "#;

//         let result = match ModuleBuilder::from_src(src, Path::from("test")) {
//             Ok(result) => result,
//             Err(errors) => {
//                 panic!(
//                     "ModuleBuilder::build_from_src failed with errors: {:?}",
//                     errors
//                 );
//             }
//         };

//         println!("symbol map: {:#?}", result.symbol_map);

//         // find the impl def
//         let impl_def = result.symbol_map.iter().find(|(_, target)| {
//             target.path.to_string() == "test::int::foo"
//                 && matches!(target.role, SymbolRole::Definition)
//         });
//         assert!(impl_def.is_some(), "Definition for int::foo not found");
//     }
// }

use std::{collections::HashSet, ops::Deref};

use crate::{
    ast::{
        self,
        asm::{AsmOp, AsmOperand},
        token::IntegerBase,
        CurlyElement, Decl, Expr, Literal, Module, Node, Path, Pattern,
    },
    graph::Graph,
    ssa::{self, SSABuilder},
    typing::{ty::Ty, TyCtx},
};

pub trait ToSSAForm<Ctx = SSABuilder> {
    type Output;

    fn to_ssa(&self, ctx: &mut Ctx, tcx: &mut TyCtx) -> Self::Output;
}

impl ToSSAForm<SSAGlobalCtx> for Module<Expr, Decl> {
    type Output = ();

    fn to_ssa(&self, gcx: &mut SSAGlobalCtx, tcx: &mut TyCtx) -> Self::Output {
        self.decls.to_ssa(gcx, tcx);
    }
}

impl ToSSAForm<SSAGlobalCtx> for Node<Decl> {
    type Output = ();

    fn to_ssa(&self, gcx: &mut SSAGlobalCtx, tcx: &mut TyCtx) -> Self::Output {
        let id = self.id;
        match &self.value {
            Decl::Fn(func) => {
                let mut ctx = SSABuilder::new();

                // add the parameters to the function
                let mut param_tys = vec![];
                for p in func.sig.params.iter() {
                    let name = p.name().unwrap().to_string();
                    let ty = tcx.mk_tvar(p.id);
                    param_tys.push(ty.clone());
                    ctx.param(name, ty);
                }

                let body = func.body.as_ref().unwrap();
                let loc = if !matches!(body.value, Expr::Block(_)) {
                    let (_, loc) = ctx.with_new_block(|ctx| body.to_ssa(ctx, tcx));
                    loc
                } else {
                    body.to_ssa(&mut ctx, tcx)
                };
                let ret_ty = if loc.id != 0 {
                    tcx.ty_of(loc.id)
                } else {
                    Ty::unit()
                };

                ctx.with_exit_block(|ctx| {
                    ctx.ret(loc);
                });

                let ty = Ty::Func(param_tys, Box::new(ret_ty));
                tcx.set_ty(id, ty);

                let name = func.sig.path.clone();
                let (params, locals, blocks, data, cfg) = ctx.done();
                gcx.add_func(id, name, params, locals, blocks, data, cfg);
            }
            Decl::Mutable(_) | Decl::Name(_) => {
                todo!()
            }
            Decl::Trait(tr) => {
                for func in tr.funcs.iter() {
                    gcx.add_trait_member(func.path.clone());
                }
            }
            Decl::Impl(_) => todo!(),
            Decl::Extern(ext) => {
                let ty = tcx.mk_tvar(id);
                let decl = ext.decl();
                let src = ext.src();
                match ext.decl() {
                    Decl::Mutable(name) | Decl::Name(name) => {
                        let is_mutable = matches!(decl, Decl::Mutable(_));
                        gcx.new_extern(name.path.clone(), ty, is_mutable, src.clone());
                    }
                    Decl::FnSig(sig) => {
                        gcx.new_extern(sig.path.clone(), ty, false, src.clone());
                    }
                    d @ _ => unreachable!("to_ssa Decl::Extern: {:?}", d),
                }
            } // TODO?
            Decl::Declare(_) => todo!(),
            Decl::FnSig(_) => todo!(),
            Decl::TypeAlias(_, _) | Decl::Struct(_) => {}
        }
    }
}

pub struct SSAGlobalCtx {
    pub funcs: Vec<Node<ssa::Func>>,
    pub externs: Vec<ssa::Extern>,
    pub trait_member_set: HashSet<Path>,
}

impl SSAGlobalCtx {
    fn add_func(
        &mut self,
        id: u64,
        name: Path,
        params: Vec<(String, Ty)>,
        locals: Vec<ssa::Local>,
        blocks: Vec<ssa::Block>,
        data: Vec<Vec<u8>>,
        cfg: Graph<usize, HashSet<usize>>,
    ) {
        self.funcs.push(Node::with_id(
            id,
            ssa::Func {
                name,
                params,
                locals,
                blocks,
                data,
                cfg,
            },
        ));
    }

    fn new_extern(&mut self, name: Path, ty: Ty, is_mutable: bool, src: Option<String>) {
        self.externs.push(ssa::Extern {
            name,
            ty,
            is_mutable,
            src,
        });
    }

    fn add_trait_member(&mut self, name: Path) {
        self.trait_member_set.insert(name);
    }
}

impl ToSSAForm for Node<Expr> {
    type Output = Node<usize>;

    fn to_ssa(&self, ctx: &mut SSABuilder, tcx: &mut TyCtx) -> Self::Output {
        let id = self.id;
        match &self.value {
            Expr::Pattern(_) => todo!(),
            Expr::Path(v) => (id, v).to_ssa(ctx, tcx),
            Expr::Name(n) => (id, &n.path).to_ssa(ctx, tcx),
            Expr::Literal(lit) => (id, lit).to_ssa(ctx, tcx),
            Expr::Cast(c) => c.lhs.to_ssa(ctx, tcx),
            Expr::Paren(ex) | Expr::TypeAnnotated(ex, _) => {
                let res = ex.to_ssa(ctx, tcx);
                let ty = tcx.ty_of(res.id);
                tcx.set_ty(id, ty);
                res
            }
            Expr::Range(range) => {
                // create a `range` struct
                //  - start: T
                //  - end: T
                //  - inclusive: bool
                let ty = tcx.mk_tvar(id);
                let loc = ctx.local(ty.clone());
                ctx.set(Node::new(loc), ssa::malloc(ssa::Value::Sizeof(ty)));

                // store the start value
                let start_ty = tcx.mk_tvar(range.start.id);
                let start_loc = range.start.to_ssa(ctx, tcx);
                let size = ssa::Value::Sizeof(start_ty);
                let mut offset = ssa::Value::zero();
                ctx.store(
                    loc,
                    ssa::Value::Local(*start_loc),
                    size.clone(),
                    offset.clone(),
                );

                offset += size;

                // store the end value
                let end_ty = tcx.mk_tvar(range.end.id);
                let end_loc = range.end.to_ssa(ctx, tcx);
                let size = ssa::Value::Sizeof(end_ty.clone());
                ctx.store(
                    loc,
                    ssa::Value::Local(*end_loc),
                    size.clone(),
                    offset.clone(),
                );

                offset += size;

                // store the inclusive flag
                ctx.store(
                    loc,
                    ssa::Value::Uint(
                        if matches!(range.limits, ast::RangeLimits::Inclusive) {
                            1
                        } else {
                            0
                        },
                        Ty::bool(),
                    ),
                    ssa::Value::Sizeof(Ty::bool()),
                    offset.clone(),
                );

                Node::with_id(id, loc)
            }
            Expr::Tuple(tuple) => {
                let size = tuple.seq.items.len();
                let mut el_tys = vec![];
                for el in tuple.seq.items.iter() {
                    el_tys.push(tcx.mk_tvar(el.id));
                }
                let ty = Ty::Tuple(el_tys);
                tcx.set_ty(id, ty.clone());

                // create a new local for the tuple and then make an allocation
                let tuple_loc = ctx.local(ty.clone());
                if size != 0 {
                    ctx.set(
                        Node::with_id(id, tuple_loc),
                        ssa::malloc(ssa::Value::Sizeof(ty)),
                    );

                    // for each element of the tuple, store it on the stack
                    let mut offset = ssa::Value::Uint(0, Ty::uint());
                    for el in tuple.seq.items.iter() {
                        // generate the lir for the element
                        let el_loc = el.to_ssa(ctx, tcx);
                        let el_ty = tcx.ty_of(el.id);

                        // store the element on the stack
                        let size = ssa::Value::Sizeof(el_ty.clone());
                        ctx.store(
                            tuple_loc,
                            ssa::Value::Local(*el_loc),
                            size.clone(),
                            offset.clone(),
                        );

                        offset += size;
                    }
                } else {
                    ctx.set(
                        Node::with_id(id, tuple_loc),
                        ssa::malloc(ssa::Value::Sizeof(ty)),
                    );
                };

                Node::with_id(id, tuple_loc)
            }
            Expr::List(list) => {
                let el_ty = Ty::Var(tcx.tf().next());
                let ty = Ty::list(el_ty.clone());
                tcx.set_ty(id, ty.clone());

                // allocate memory for the values
                let item_count = list.items.len();
                let capacity = item_count * 3;
                let values_ty = Ty::ptr(el_ty.clone());
                let values_loc = ctx.local(values_ty.clone());
                ctx.set(
                    Node::new(values_loc),
                    ssa::malloc(ssa::Value::Sizeof(el_ty.clone()) * capacity),
                );

                let mut offset = ssa::Value::Uint(0, Ty::uint());
                for item in list.items.iter() {
                    let item_loc = item.to_ssa(ctx, tcx);
                    let item_ty = tcx.ty_of(item.id);
                    let size = ssa::Value::Sizeof(item_ty);
                    ctx.store(
                        values_loc,
                        ssa::Value::Local(*item_loc),
                        size.clone(),
                        offset.clone(),
                    );
                    offset += size;
                }

                // allocate space for the list struct
                //   - values ptr: *'a
                //   - len: uint
                //   - capacity: uint
                let list_loc = ctx.local(ty.clone());
                ctx.set(
                    Node::new(list_loc),
                    ssa::malloc(ssa::Value::PointerSize * 3),
                );

                // store the values ptr
                ctx.store(
                    list_loc,
                    ssa::Value::Local(values_loc),
                    ssa::Value::Sizeof(values_ty.clone()),
                    ssa::Value::zero(),
                );

                // store the length
                ctx.store(
                    list_loc,
                    ssa::Value::Uint(item_count as u64, Ty::uint()),
                    ssa::Value::PointerSize,
                    ssa::Value::PointerSize,
                );

                // store the capacity
                ctx.store(
                    list_loc,
                    ssa::Value::Uint(capacity as u64, Ty::uint()),
                    ssa::Value::PointerSize,
                    ssa::Value::PointerSize * 2,
                );

                Node::with_id(id, list_loc)
            }
            Expr::Asm(asm) => {
                let ty = tcx.mk_tvar(id);
                let mut binops = asm
                    .inst
                    .iter()
                    .map(|(op, rands)| match op {
                        AsmOp::Malloc => ssa::malloc(match &rands[0] {
                            AsmOperand::Var(name) => {
                                let loc = ctx
                                    .get_var(name)
                                    .expect(&format!("cannot find variable: {}", name));
                                ssa::Value::Local(loc)
                            }
                            AsmOperand::Int(i) => ssa::Value::Uint(*i, Ty::uint()),
                        }),
                        _ => {
                            let mut binop = ssa::BasicOp::from(*op);
                            binop.operands.extend(rands.iter().map(|rand| match rand {
                                AsmOperand::Var(name) => {
                                    let loc = ctx
                                        .get_var(name)
                                        .expect(&format!("cannot find variable: {}", name));
                                    ssa::Value::Local(loc)
                                }
                                AsmOperand::Int(i) => ssa::Value::Uint(*i, Ty::uint()),
                            }));
                            Node::new(ssa::Value::BasicOp(binop))
                        }
                    })
                    .collect::<Vec<_>>();

                let last = binops.pop().unwrap();
                let loc = if let ssa::Value::Local(loc) = last.deref() {
                    *loc
                } else {
                    let loc = ctx.local(ty.clone());
                    ctx.set(Node::with_id(id, loc), last);
                    loc
                };

                Node::with_id(id, loc)
            }
            Expr::Curly(curly) => {
                let ty = &curly.ty;
                let loc = ctx.local(ty.clone());
                tcx.set_ty(id, ty.clone());
                ctx.set(
                    Node::with_id(id, loc),
                    ssa::malloc(ssa::Value::Sizeof(ty.clone())),
                );

                let mut offset = ssa::Value::zero();
                for field in curly.elements.iter() {
                    let (_, field_value) = variant!(&field.value, if CurlyElement::Labeled(x, y));
                    let field_loc = field_value.to_ssa(ctx, tcx);
                    let field_ty = tcx.ty_of(field_loc.id);
                    let field_size = ssa::Value::Sizeof(field_ty);
                    ctx.store(
                        loc,
                        ssa::Value::Local(*field_loc),
                        field_size.clone(),
                        offset.clone(),
                    );
                    offset += field_size;
                }

                Node::with_id(id, loc)
            }
            Expr::Block(block) => {
                let (_, mut locs) = ctx.with_new_block(|ctx| block.stmts.to_ssa(ctx, tcx));
                if let Some(last_loc) = locs.pop() {
                    last_loc
                } else {
                    Node::with_id(0, 0)
                }
            }
            // HirNode::DerefAssign(lhs, rhs) => {
            //     let info = info.src_info().clone();
            //     let (mut inst, rhs_val) = rhs.to_ssa(ctx, tcx);
            //     let rhs_loc = ctx.get_or_set_local(rhs_val, info.clone(), rhs.ty(), &mut inst);
            //     let (lhs_inst, lhs_val) = lhs.to_ssa(ctx, tcx);
            //     inst.extend(lhs_inst);
            //     let size = rhs.ty().size_of();
            //     let lhs_loc = ctx.get_or_set_local(lhs_val, info.clone(), lhs.ty(), &mut inst);
            //     ctx.push(Node::new(
            //         lir::Store::new(
            //             ssa::Value::Local(lhs_loc),
            //             ssa::Value::Local(rhs_loc),
            //             ssa::Value::zero(),
            //             size,
            //         ),
            //         info,
            //     ));
            //     (inst, lir::Value::Empty)
            // }
            Expr::Assign(assign) => {
                (&assign.lhs, assign.rhs.as_ref()).to_ssa(ctx, tcx);

                // // generate the RHS
                // let rhs_loc = assign
                //     .rhs
                //     .to_ssa(ctx, tcx);

                // // then the LHS
                // let lhs_loc = assign.lhs.to_ssa(ctx, tcx);

                // let Node {
                //     id,
                //     value: loc,
                // } = &mut rhs_loc;
                // // re-identify the node
                // let ty = tcx.ty_of(*id);
                // *id = assign.lhs.id;
                // tcx.set_ty(*id, ty);
                // ctx.set_var_loc(name,)

                // ctx.set(lhs_loc, rhs_val);
                Node::with_id(0, 0)
            }
            Expr::Fn(_) => todo!(),
            Expr::Dot(dot) => {
                let lhs_loc = dot.lhs.to_ssa(ctx, tcx);
                let ret_ty = tcx.mk_tvar(id);
                let loc = ctx.local(ret_ty.clone());
                ctx.set(
                    Node::with_id(id, loc),
                    Node::new(ssa::Value::FieldOf(lhs_loc, dot.rhs.path.to_string())),
                );

                Node::with_id(id, loc)
            }
            Expr::Call(call) => {
                let mut call_args = vec![];
                let mut arg_tys = vec![];
                let fn_name = if let Expr::Dot(dot) = &call.lhs.value {
                    let lhs = dot
                        .lhs
                        .to_ssa(ctx, tcx)
                        .take_map(|loc| ssa::Value::Local(loc));
                    let lhs_ty = tcx.ty_of(lhs.id);
                    arg_tys.push(lhs_ty.clone());
                    call_args.push(lhs);
                    Some(
                        lhs_ty
                            .get_path()
                            .unwrap()
                            .append(dot.rhs.path.name().unwrap()),
                    )
                } else {
                    call.lhs.path()
                };

                for arg in call.args.items.iter() {
                    let arg_loc = arg.to_ssa(ctx, tcx).take_map(|loc| ssa::Value::Local(loc));
                    arg_tys.push(tcx.ty_of(arg.id));
                    call_args.push(arg_loc);
                }

                let callable = if let Some(fn_name) = fn_name {
                    // ctx.add_sym(fn_name.clone());
                    ssa::Callable::Name(fn_name)
                } else {
                    todo!("call ref")
                };

                let ret_ty = tcx.mk_tvar(id);
                let fn_ty = Ty::Func(arg_tys, Box::new(ret_ty.clone()));
                tcx.set_ty(call.lhs.id, fn_ty);

                let ty = Ty::Var(tcx.tf().next());
                let loc = Node::new(ctx.local(ty.clone()));
                tcx.set_ty(loc.id, ty);
                ctx.set(
                    loc.clone(),
                    Node::with_id(
                        id,
                        ssa::Value::Call(Node::with_id(call.lhs.id, callable), call_args),
                    ),
                );

                loc
            }
            Expr::BinOp(_) => todo!("to_ssa: Expr::BinOp: {}", self),
            Expr::Break(_) => todo!("to_ssa: Expr::Break: {}", self),
            Expr::Closure(_) => todo!("to_ssa: Expr::Closure: {}", self),
            Expr::DefaultValue(_) => todo!("to_ssa: Expr::DefaultValue: {}", self),
            Expr::For(_) => todo!("to_ssa: Expr::For: {}", self),
            Expr::If(if_ex) => {
                let ty = tcx.mk_tvar(id);
                let (cond_label, cond_loc) = ctx.with_new_block(|ctx| if_ex.cond.to_ssa(ctx, tcx));
                let (then_label, then_loc) = ctx.with_new_block(|ctx| if_ex.then.to_ssa(ctx, tcx));
                let (else_label, else_loc) = ctx.with_new_block(|ctx| {
                    if let Some(else_ex) = if_ex.els.as_deref() {
                        else_ex.to_ssa(ctx, tcx)
                    } else {
                        let else_loc = ctx.local(Ty::nil());
                        ctx.set(
                            Node::new(else_loc),
                            Node::new(ssa::Value::Uint(0, Ty::nil())),
                        );
                        Node::new(else_loc)
                    }
                });

                // branch to the then and else blocks
                ctx.with_block(cond_label, |ctx| {
                    ctx.cond_branch(cond_loc, then_label, else_label)
                });

                let (end_label, if_loc) = ctx.with_new_block(|ctx| {
                    let if_loc = ctx.local(ty);
                    ctx.phi(
                        Node::with_id(id, if_loc),
                        vec![(then_label, then_loc), (else_label, else_loc)],
                    );
                    if_loc
                });

                ctx.with_block(then_label, |ctx| ctx.goto(end_label));
                ctx.with_block(else_label, |ctx| ctx.goto(end_label));

                // use this block for the next instructions
                ctx.use_block(end_label);

                Node::with_id(id, if_loc)
            }
            Expr::Index(_) => todo!("to_ssa: Expr::Index: {}", self),
            Expr::Labeled(_, _) => todo!("to_ssa: Expr::Labeled: {}", self),
            Expr::Loop(_) => todo!("to_ssa: Expr::Loop: {}", self),
            Expr::Return(_) => todo!("to_ssa: Expr::Return: {}", self),
            Expr::Sequence(_) => todo!("to_ssa: Expr::Sequence: {}", self),
            Expr::Type(_) => todo!("to_ssa: Expr::Type: {}", self),
            Expr::UnaryOp(_) => todo!("to_ssa: Expr::UnaryOp: {}", self),
            Expr::Unsafe(_) => todo!("to_ssa: Expr::Unsafe: {}", self),
            Expr::While(_) => todo!("to_ssa: Expr::While: {}", self),
        }
    }
}

impl ToSSAForm for (&Node<Pattern>, &Node<Expr>) {
    type Output = ();

    fn to_ssa(&self, ctx: &mut SSABuilder, tcx: &mut TyCtx) -> Self::Output {
        let &(lhs, rhs) = self;
        match &lhs.value {
            Pattern::Name(v) => {
                let name = v.to_string();
                let rhs_loc = rhs.to_ssa(ctx, tcx);
                let _ = tcx.mk_tvar(lhs.id);
                if let Some(lhs_loc) = ctx.get_var_loc(&name) {
                    ctx.block().def_var(lhs_loc);
                    ctx.set(
                        Node::with_id(lhs.id, lhs_loc),
                        rhs_loc.take_map(|loc| ssa::Value::Local(loc)),
                    );
                } else {
                    // a new variable here
                    ctx.set_var_loc(name, *rhs_loc);
                }
            }
            Pattern::Deref(_) => todo!(),
            Pattern::Sequence(_) => todo!(),
            Pattern::Tuple(_) => todo!(),
        }
    }
}

impl ToSSAForm for (u64, &Path) {
    type Output = Node<usize>;

    fn to_ssa(&self, ctx: &mut SSABuilder, tcx: &mut TyCtx) -> Self::Output {
        let &(id, path) = self;
        let name = path.to_string();
        let _ = tcx.mk_tvar(id);
        Node::with_id(
            id,
            if let Some(loc) = ctx.get_var(&name) {
                loc
            } else {
                panic!("cannot use variable before it's defined: {}", name)
            },
        )
    }
}

impl ToSSAForm for (u64, &Literal) {
    type Output = Node<usize>;

    fn to_ssa(&self, ctx: &mut SSABuilder, tcx: &mut TyCtx) -> Self::Output {
        let &(id, lit) = self;
        let ty = tcx.mk_tvar(id);

        let val = match lit {
            Literal::Integer {
                value,
                base,
                size,
                signed,
            } => match base {
                IntegerBase::Decimal => {
                    let ty = match (*size, *signed) {
                        (8, true) => Ty::i8(),
                        (16, true) => Ty::i16(),
                        (32, true) => Ty::i32(),
                        (64, true) => Ty::i64(),
                        (8, false) => Ty::u8(),
                        (16, false) => Ty::u16(),
                        (32, false) => Ty::u32(),
                        (64, false) => Ty::u64(),
                        (_, true) => Ty::int(),
                        (_, false) => Ty::uint(),
                    };

                    if *signed {
                        let c = value.parse::<i64>().unwrap();
                        ssa::Value::Int(c, ty)
                    } else {
                        let c = value.parse::<u64>().unwrap();
                        ssa::Value::Uint(c, ty)
                    }
                }
                IntegerBase::Binary => todo!(),
                IntegerBase::Octal => todo!(),
                IntegerBase::Hex => todo!(),
            },
            Literal::Float { .. } => todo!(),
            Literal::String(s) => {
                // convert the string to bytes and add a `Data` to the program
                let bytes = s.as_bytes().to_vec();
                let len = bytes.len();
                let idx = ctx.data(bytes);

                // store the size in a variable so we can re-use it
                let size_loc = ctx.local(Ty::uint());
                ctx.set(
                    Node::new(size_loc),
                    Node::new(ssa::Value::Uint(len as u64, Ty::uint())),
                );

                // allocate a pointer to store the string bytes
                let data_loc = ctx.local(Ty::ptr(Ty::u8()));
                let ptr = ssa::malloc(size_loc);
                ctx.set(Node::new(data_loc), ptr);

                // make a call to `memcpy` to copy the bytes
                let memcopy_loc = Node::new(ctx.local(Ty::uint()));
                ctx.set(
                    memcopy_loc,
                    ssa::memcopy(data_loc, idx, ssa::Value::Local(size_loc)),
                );

                // create a `string` struct
                //  - raw_ptr: *u8
                //  - size: usize
                let loc = ctx.local(Ty::string());
                let ptr = ssa::malloc(ssa::Value::PointerSize * 2);
                ctx.set(Node::with_id(id, loc), ptr);

                // store the pointer to the bytes
                ctx.store(
                    loc,
                    ssa::Value::Local(data_loc),
                    ssa::Value::zero(),
                    ssa::Value::PointerSize,
                );

                // store the size of the string
                ctx.store(
                    loc,
                    ssa::Value::Local(size_loc),
                    ssa::Value::PointerSize,
                    ssa::Value::PointerSize,
                );

                return Node::with_id(id, loc);
            }
            Literal::ByteString(_) => todo!(),
            Literal::Byte(_) => todo!(),
            Literal::Char(ch) => ssa::Value::Uint(*ch as u64, Ty::char()),
            Literal::Bool(b) => ssa::Value::Uint(if *b { 1 } else { 0 }, Ty::bool()),
            Literal::UnicodeEscSeq(_) => todo!(),
            Literal::Unit => ssa::Value::Uint(0, Ty::unit()),
            Literal::Nil => ssa::Value::Uint(0, Ty::nil()),
        };

        let loc = ctx.local(ty);
        ctx.set(Node::with_id(id, loc), Node::new(val));
        Node::with_id(id, loc)
    }
}

impl ToSSAForm for Vec<Node<Expr>> {
    type Output = Vec<Node<usize>>;

    fn to_ssa(&self, ctx: &mut SSABuilder, tcx: &mut TyCtx) -> Self::Output {
        self.iter().map(|t| t.to_ssa(ctx, tcx)).collect::<Vec<_>>()
    }
}

impl ToSSAForm<SSAGlobalCtx> for Vec<Node<Decl>> {
    type Output = ();

    fn to_ssa(&self, gtx: &mut SSAGlobalCtx, tcx: &mut TyCtx) -> Self::Output {
        for d in self.iter() {
            d.to_ssa(gtx, tcx);
        }
    }
}

# Ray Type System (Living Specification)

Ray is an imperative, WASI‑first language with strong, inference‑friendly static typing.

## 0. Philosophy and Goals

This document is for Ray contributors and implementors. Its goal is to describe the internal architecture, invariants, and algorithms of the type system well enough that the checker can be implemented, debugged, and evolved from this description.

- **Primary goal: predictable local reasoning**
  A programmer should be able to understand the types of a function or item by looking at its definition, its explicit signature (if any), and its trait bounds, without needing to understand the whole program. Inference should feel like a convenience layer over a clear, explicit model, not a source of surprises.

- **Binding-group–oriented solving**
  Ray uses a single mode of solving based on *binding groups*. Each group (a set of mutually recursive bindings) is type‑checked in isolation using a structure‑aware constraint tree inspired by OutsideIn(X):
  - Each node in this tree carries **givens** (assumed constraints) and **wanteds** (obligations to solve).
  - Solving proceeds from the leaves upward, discharging wanteds against available givens and global instances, and propagating residual constraints to enclosing scopes.
  - This replaces the old "global constraint soup" with a scoped, per‑group discipline.

- **Relationship to Rust, Haskell, and ML**
  - Like Rust, Ray uses trait‑based ad‑hoc polymorphism, item isolation for trait/impl methods, and value‑restricted generalization. Trait and impl methods must be fully annotated and are solved as their own binding groups.
  - Like Haskell, Ray supports multi‑parameter traits and unannotated function definitions, and uses class‑like predicates in constraints. However, Ray does *not* expose functional dependencies, type families, or user‑visible injectivity; equalities between trait parameters arise only from use sites.
  - Unlike traditional ML, Ray does not offer unconstrained let‑polymorphism for arbitrary expressions; only syntactic values generalize, and generalization is tied to binding groups.

- **Multi-parameter traits with receiver first**
  Ray traits are multi‑parameter but Rust‑flavored: the first parameter is always the *receiver* type. The solver does not assume any global functional dependencies or injectivity between the remaining parameters. Any equalities between trait parameters are derived *only* from how a trait appears in a particular context. For example, if a trait `C[a, b]` is used as a qualifier in `forall t. C[t, t]`, then within that quantified context the solver may treat `a == b`, but that equality does not become a global property of `C`.

- **Defaulting is late and cosmetic**
  Traits may opt into defaulting via a language‑level `default(T)` marker. Defaulting runs late in the pipeline, after normal constraint and trait solving, and is allowed only to fill in otherwise unconstrained meta variables using these declared defaults. Defaulting must not perform real inference or change which programs type‑check; it only resolves remaining ambiguities in a predictable, trait‑directed way.

- **Unannotated free functions are not a special mode**
  Ray allows unannotated top‑level free functions, providing a smoother, more Haskell‑like experience where appropriate, but they are still processed by the same binding‑group solver as everything else. Annotated items (such as trait and impl methods) form singleton binding groups with fully specified types; unannotated functions participate in binding‑group analysis to infer their types, but do not switch the system into a different "script mode." This keeps the mental model uniform while still offering ergonomic inference where it is safe.

---

## 1. Core Concepts

### 1.1 Types
From the solver's point of view, types are syntactic trees built from:

- **Primitive types**
  Built-in closed types such as integers, floats, booleans, unit, and platform-specific primitives. Each primitive is a nullary type constructor with no internal structure visible to the unifier beyond "same/ different primitive."

- **Function types**
  `(T0, T1, …) -> Tn`, with zero or more argument types and a single result type. The solver treats them structurally: two function types unify by unifying their argument lists element-wise and their result types.

- **Pointer types**
  - `*T` for safe references.
  - `rawptr[T]` for unsafe raw pointers.
  Both are ordinary unary constructors as far as the unifier is concerned; auto-ref/deref behavior for receivers is modelled via `Recv` predicates (Section 2.4), not special-cased in equality.

- **Record types**
  Nominal or structural record types with named fields. The unifier typically treats record constructors nominally (two different record types do not unify), while field-level reasoning (e.g. projecting `foo` from `r`) is done via `HasField` predicates (Section 2.3).

- **Nilable types**
  `nilable[T]` is a unary constructor representing an optional value of type `T`. Values of this type are constructed with either `some(e)` (present value) or `nil` (absence). Any special behavior (e.g. pattern exhaustiveness) is handled at higher layers; the unifier treats `nilable` like any other unary type constructor.

Type schemes and qualifier lists (e.g. `forall[a]. P => T`) are described in Section 3; in the core constraint language we work with monomorphic types built from the above constructors and type variables.

### 1.2 Type Variables
Ray uses several flavors of type variables internally, with different roles and invariants:

- **Flexible (meta) variables**
  - Notation (internal): `?α`, `?β`, …
  - Introduced during inference to stand for unknown types.
  - May be unified with arbitrary types, subject to occurs-check, and are ultimately solved to a concrete type or left unsolved for generalization/defaulting.
  - Only metas may appear on the left-hand side of unifier substitutions.

- **Rigid variables**
  - Notation: `'a`, `'b`, … (bound by signatures or type parameters).
  - Represent universally quantified parameters that are fixed for the duration of checking a binding or item.
  - Metas may unify *to* a rigid, but two distinct rigids are never equated by inference; attempting to do so is a type error.

- **Skolem variables**
  - Introduced by skolemization (Section 3.3) when checking against explicit polymorphic annotations.
  - Behave like rigid variables, but additionally carry a scope marker so we can detect skolem escape (Section 9.3).
  - Any attempt to unify a skolem with a type that would let it escape its scope is rejected.

- **Schema variables (quantified variables)**
  - These are the logical binders in a type scheme `forall[a1..an]. P => T`.
  - They never appear directly in constraints; they are placeholders that are instantiated to metas (at use sites) or skolem vars (when checking annotations).

The solver must maintain the invariant that only metas are ever solved, while rigids and skolems remain fixed names whose only role is to constrain what metas and concrete types are allowed.

### 1.3 Terms
For type checking we distinguish three main syntactic categories:

- **Expressions**
  Term-level constructs that produce values and types: literals, function calls, field access, control flow, etc. Expression typing generates equality and predicate constraints and attaches them to nodes in the constraint tree for the current binding group.

- **Patterns**
  Destructuring forms used in bindings, `match` arms, parameter lists, etc. Patterns both introduce new term bindings and yield **givens** about the scrutinee's shape (e.g. which variant of an enum, which fields are present). These givens become part of the node's constraint context.

- **Bindings and binding groups**
  Named definitions (`x = e`, `mut x = e`, top-level items, trait/impl methods) are grouped into **binding groups**, which are the unit of term solving and generalization:
  - A binding group is a maximal set of mutually recursive bindings in the same lexical scope. Two bindings `f` and `g` are in the same group if there is a path of references `f -> … -> g` and `g -> … -> f` using only names defined in that scope.
  - The compiler builds binding groups by:
    - Collecting all bindings in a scope (top-level, function body, block).
    - Building a directed dependency graph where each binding has edges to other bindings it references in the same scope.
    - Computing strongly connected components (SCCs) of this graph; each SCC is a binding group.
     - Solving binding groups in a topological order over the SCC graph (so a group can refer to earlier groups but not vice versa).
  - Trait and impl methods are forced into singleton binding groups and are checked against their declared schemes; they do not participate in mutual recursion with other bindings.
  - Free functions and local bindings (annotated or unannotated) participate in standard binding-group analysis and may be mutually recursive within their scope. For annotated free functions, the declared scheme is treated as fixed during solving; unannotated neighbors can still be inferred using that scheme.

The term and goal solvers (Section 5) always operate on one binding group at a time, using this pre-computed grouping as their unit of work.

Pseudo-code sketch for building binding groups in a scope:

```rust
fn build_binding_groups(scope: &Scope) -> Vec<BindingGroup> {
  let bindings = scope.collect_bindings(); // names and their ASTs
  let mut graph = DepGraph::new();

  for b in &bindings {
    graph.add_node(b.name.clone());
  }

  for b in &bindings {
    let deps = free_binding_refs(&b.expr, &bindings);
    for dep in deps {
      graph.add_edge(b.name.clone(), dep);
    }
  }

  let sccs = graph.strongly_connected_components();
  sccs
    .into_iter()
    .map(|component| BindingGroup::from_nodes(component, &bindings))
    .collect()
}
```

---

## 2. Constraint Language

### 2.1 Equality Constraints
Equality constraints express that two types must be the same:

- Form: `t1 == t2`, where `t1` and `t2` may contain type constructors, metas, rigids, and skolems.
- Solved by unification, producing substitutions for metas or failing with a type-mismatch error.
- May appear as:
  - **Givens**, arising from pattern structure, explicit type annotations, or schema-derived equalities (e.g. from `C[t, t]`).
  - **Wanteds**, generated when the typing rules require two types to coincide (e.g. argument vs parameter, branch types in `if`, etc.).
Equality is the backbone of inference; other constraint forms (e.g. trait predicates) often generate or depend on these equalities.

### 2.2 Class Predicates
Class predicates represent trait obligations. Internally, we treat them as n‑ary predicates with the first argument being the receiver type:

- Form: `C[Recv, A1, …, An]`
  - `C` is a trait name.
  - `Recv` is the receiver type (first parameter, Rust-style).
  - `A1..An` are additional type arguments.
- Class predicates may appear:
  - In type schemes as qualifiers `P` in `forall[a]. P => T`.
  - As **givens**, from trait bounds on items, where-clauses, or skolemized signatures.
  - As **wanteds**, from method calls, operator use, literal overloading, and other sites that require an instance.
- Ray does not assume any global functional dependencies or injectivity between these parameters. Equalities between parameters are derived only from specific usages, such as a qualifier `forall t. C[t, t]`, which allows the solver to treat the corresponding arguments as equal *within that context*.

Examples of trait shapes in Ray include:

- `Int['a]` and `Float['a]` for numeric literals.
- `Index[Container, Elem, Index]` for indexing operations (Section A.3).
- `Iter['a, 'el]` for iteration, used by `for` loops (Section A.7).

The goal solver (Section 5.2) resolves class predicates using the instance environment and available givens, producing evidence or reporting unsatisfied obligations.

### 2.3 HasField Predicates
`HasField` models record field access and construction at the constraint level:

- Form: `HasField[RecordTy, FieldName, FieldTy]`.
- Intuition: values of type `RecordTy` have a field named `FieldName` with type `FieldTy`.
- Generated as:
  - **Wanteds** when projecting `e.field` or constructing records that must supply certain fields.
  - **Givens** when pattern-matching on records or when record types themselves carry structural field information.

`HasField` is **not user-extensible**: it is determined entirely by nominal struct declarations. The goal solver resolves `HasField` predicates by consulting the known field layout of the declared record type; users cannot add new `HasField` "instances" in the way they can for traits.

### 2.4 Recv Predicates
`Recv` models auto-ref/deref and receiver adjustment for method calls and certain operators:

- Form: `Recv[RecvTy, ExprTy]`.
- Intuition: an expression of type `ExprTy` can be coerced by a sequence of reference/dereference operations into a receiver of type `RecvTy`.
- Generated as **wanteds** at sites where method resolution or operator overloading requires a particular receiver shape but the source expression may be more or less indirected than needed.

`Recv` is also **not user-extensible**: there is a fixed, built-in set of legal auto-ref/deref steps the solver may use (e.g. going between `T` and `*T` where appropriate), and users cannot define new `Recv` behaviors via traits or instances. If no legal adjustment exists from `ExprTy` to `RecvTy`, the `Recv` predicate remains unsatisfied and ultimately yields a type error at the binding-group root (e.g. for an expression like `42.m()` with no valid receiver type).

### 2.5 Unification

The unifier is responsible for solving equality constraints `t1 == t2` by producing a substitution for meta variables. It is shared by the term solver and the goal solver.

- **Key invariants**
  - Only metas (`?α`) are ever assigned in the substitution.
  - Rigid variables and skolems are never equated with distinct types; attempting to do so is a type error.
  - The unifier enforces an occurs check to avoid infinite types.

- **Structural behavior**
  - Primitive types unify only with themselves.
  - The distinguished constant type `never` acts as a bottom type:
    - `never` unifies with any other type without constraining that type.
    - Unifying `never` with `T` produces no new substitution bindings; it simply treats the branch as non-returning.
  - Function types `(A0, …, An) -> R` unify by unifying argument lists element-wise and result types; arity mismatches cause failure.
  - Pointer types `*T` and `rawptr[T]` unify structurally:
    - `*T` with `*U` by unifying `T` and `U`.
    - `rawptr[T]` with `rawptr[U]` by unifying `T` and `U`.
    - `*T` never unifies with `rawptr[U]`.
  - Record types are nominal: two record types unify only if they have the same constructor name; field layout is handled by `HasField`, not unification.
  - `nilable[T]` unifies structurally with `nilable[U]` by unifying `T` and `U`.

- **Metas and rigids/skolems**
  - Unifying a meta `?α` with a type `T`:
    - Fails if `T` contains `?α` (occurs check).
    - Otherwise extends the substitution with `?α := T`.
  - Unifying two metas merges them, typically by assigning one to the other.
  - Unifying distinct rigids or skolems (e.g. `'a` with `'b`) is rejected as a type error.

- **Substitution normalization**
  - After solving, the substitution is normalized to keep it well-behaved:
    - Var→var bindings are oriented so that skolems never appear on the left-hand side; if a binding would map a skolem to a non-skolem, it is flipped.
    - Var→var chains are saturated so that applying the substitution is idempotent (no long chains of variable aliases).
  - This normalization does not change the logical meaning of the substitution; it only makes later reasoning about schemes and skolem escape simpler and more robust.

Simplified pseudo-code:

```rust
fn unify(t1: Ty, t2: Ty, subst: &mut Subst, info: &mut TypeSystemInfo) {
  let t1 = subst.apply(t1);
  let t2 = subst.apply(t2);
  match (t1, t2) {
    (Ty::Meta(a), Ty::Meta(b)) if a == b => {}
    (Ty::Meta(a), t) | (t, Ty::Meta(a)) => bind_meta(a, t, subst, info),
    (Ty::Rigid(a), Ty::Rigid(b)) if a == b => {}
    (Ty::Rigid(a), Ty::Rigid(b)) => info.equality_type_pair(&Ty::Rigid(a), &Ty::Rigid(b)),
    (Ty::Skolem(a), Ty::Skolem(b)) if a == b => {}
    (Ty::Skolem(a), Ty::Skolem(b)) => info.escaped_skolems(&[a, b]),
    (Ty::Fun(args1, ret1), Ty::Fun(args2, ret2)) if args1.len() == args2.len() => {
      for (p, q) in args1.into_iter().zip(args2.into_iter()) {
        unify(p, q, subst, info);
      }
      unify(*ret1, *ret2, subst, info);
    }
    (Ty::Ptr(t1), Ty::Ptr(t2)) => unify(*t1, *t2, subst, info),
    (Ty::RawPtr(t1), Ty::RawPtr(t2)) => unify(*t1, *t2, subst, info),
    (Ty::Nilable(t1), Ty::Nilable(t2)) => unify(*t1, *t2, subst, info),
    (Ty::Record(name1, _), Ty::Record(name2, _)) if name1 == name2 => {}
    (a, b) => info.equality_type_pair(&a, &b),
  }
}
```

The real implementation adds more cases and propagates failures appropriately, but must obey these structural and scoping rules.

---

## 3. Polymorphism and Type Schemes

### 3.1 Forall quantification
Ray uses rank-1 universal quantification to represent polymorphic types. A **type scheme** has the form:

```text
forall[a1..an]. P => T
```

- `a1..an` are **schema variables** (Section 1.2) that are universally quantified.
- `P` is a (possibly empty) list of class predicates that must hold whenever the scheme is instantiated.
- `T` is a monomorphic type built from constructors and type variables.

Key points:

- Type schemes appear:
  - In user-written annotations on functions, trait methods, and impl methods.
  - As generalized types produced at binding-group boundaries (Section 3.4).
- At use sites, schemes are instantiated to monomorphic types with metas standing in for `a1..an` (Section 3.2).
- At check sites (when a binding has an explicit annotation), schemes are skolemized to introduce rigids in place of `a1..an` (Section 3.3).

Within the solver, we always work with:

- Monomorphic types (with metas/rigids/skolems) plus
- An explicit scheme representation `forall[a1..an]. P => T` stored in the environment for generalized bindings.

### 3.2 Instantiation
Instantiation is the operation that turns a polymorphic type scheme into a monomorphic type for use at a particular site.

- Given a type scheme `forall[a1..an]. P => T`, instantiation:
  - Introduces fresh flexible meta variables `?α1.. ?αn` for the quantified variables.
  - Produces a mono type by *simultaneous substitution* of these metas for the quantified variables:
    - `T[ai := ?αi]` means "replace each `ai` in `T` with the corresponding `?αi`, all at once."
  - Emits the instantiated predicates `P[ai := ?αi]` as **wanted** constraints at the current node in the constraint tree.

Concretely, consider:

```rust
fn head['a](xs: list['a]) -> 'a where Index[list['a], 'a, uint] { xs[0] }
```

Its scheme is `forall['a]. Index[list['a], 'a, uint] => (list['a]) -> 'a`. Instantiating this scheme at a call site:

- Introduces a fresh meta `?0` for `'a`.
- Produces the mono type `(list[?0]) -> ?0`.
- Emits a wanted predicate at the call site:
  - `Index[list[?0], ?0, uint]`

This wanted is then fed into the constraint tree at the node for the call, to be solved later by the goal solver using givens and instances.

- This is performed whenever a generalized binding is *used* (e.g. variable reference, function call), unless the site demands a specific monomorphic instantiation.

Instantiation is an internal operation, not a separate constraint kind in the language.

### 3.3 Skolemization
Skolemization is the operation used when *checking* a binding against an explicit polymorphic annotation.

- Given an expected type scheme `forall[a1..an]. P => T` for a binding:
  - Introduce rigid/skolem type variables `s1..sn` standing for each `ai`.
  - Add `P[ai := si]` to the node's **givens**:
    - Here `P[ai := si]` again means "replace each quantified variable `ai` in the predicate list `P` with the corresponding skolem `si`, simultaneously."
    - These predicates now express assumptions that are guaranteed to hold throughout the binding body.
  - Check the binding body against the instantiated type `T[ai := si]`, generating equalities and additional wanted predicates as usual.

For example:

```rust
fn foo['a](x: 'a) -> bool where Int['a] { ... }
```

has scheme `forall['a]. Int['a] => ('a) -> bool`. When checking `foo`:

- Skolemization introduces a skolem `s0` for `'a`.
- Adds `Int[s0]` to the function's givens.
- Checks the body assuming `x : s0` and `Int[s0]` holds in that scope.

- Skolem variables must not escape their scope; any attempt to unify a skolem with an incompatible type should produce a skolem-escape error.

Like instantiation, skolemization is an operation tied to annotations and binding groups, not a separate polymorphism constraint.

### 3.4 Generalization

Ray uses *lexical, value-restricted generalization* to allow reusable polymorphic bindings without enabling unconstrained ML-style let-polymorphism.

#### When Ray generalizes
A binding `x = e` (or `mut x = e`) is generalized *only if*:

1. `e` is a syntactic value
   Examples:
   - `fn(a) { a }`
   - closures and function literals that do not execute code at binding time
2. All free type variables in `e`'s type are *not rigid* and are not fixed by surrounding constraints.

If so, Ray wraps the type in a type scheme:
`forall[t1..tn]. T`.

This value-restricted generalization applies to unannotated top-level free functions and local bindings. Trait and impl methods (and other explicitly annotated items) use their explicit schemes and are never generalized from inference.

We say that a binding `x` is **eligible for generalization** if it satisfies both conditions above (syntactic value, and all free type variables are flexible and unfixed). In algorithmic terms:

```rust
fn eligible_for_generalization(binding: &Binding) -> bool {
  let e = binding.rhs();
  let ty = binding.type_after_solving(); // mono type with metas
  is_syntactic_value(e)
    && all_free_type_vars_are_flexible_and_unfixed(ty)
    && binding.is_unannotated()
}
```

Only bindings that are `eligible_for_generalization` are ever turned into polymorphic schemes at a binding-group root.

Here `is_syntactic_value` is a purely syntactic predicate over the AST. For the current Ray language it is intentionally small and Rust-like:

```rust
fn is_syntactic_value(e: &Expr) -> bool {
  match e {
    // Function and closure literals
    Expr::FnLiteral { .. } => true,         // fn(a) { body }, fn(a) => body, etc.

    // Everything else is considered expansive and not a syntactic value
    _ => false,
  }
}
```

This matches the examples above:

- A closure literal or function expression is always a syntactic value, regardless of its body.
- Expressions that perform computation at binding time (calls, operators, control flow, loops, pattern `if`/`while`/`for`, etc.) are not syntactic values and therefore never generalized by the value restriction.

Numeric literals are intentionally *not* syntactic values, because their types are typically fixed by later constraints (for example, `len = 1` becomes `uint` when used as an argument to `malloc`), rather than producing a polymorphic local scheme like `forall[a]. Int[a] => a`.

#### When Ray does NOT generalize
A local binding remains **monomorphic** if:

- the right-hand side performs computation
  (`y = foo(x) + 2`)
- the binding participates in constraint solving that fixes variables
- the binding appears inside a non-value expression (control flow, match arms, loops)

#### Why this matters 
- Ray avoids the classic ML pitfall where polymorphic locals interact with effects and inference becomes unpredictable.
- But Ray still allows true polymorphism for lambdas and reusable definitions.
- This preserves Rust-like predictability while enabling inference for simple, unannotated code.

#### How this interacts with the solver
- Generalization happens at **binding-group boundaries** after local term solving, predicate solving, and defaulting have produced final types and substitutions for the group (Sections 5 and 8).
- For each binding `x` that is `eligible_for_generalization(x)`:
  - Let `Ty_x` be its type after applying the final substitution.
  - Let `F` be the set of flexible meta variables that still appear in `Ty_x`.
  - Let `P_qual` be the subset of solved predicates the solver intends to attach as qualifiers, restricted to those whose free type variables are all contained in `F`.
  - The generalized scheme for `x` is:

    ```text
    forall F. P_qual => Ty_x
    ```

  In other words, a predicate is allowed into a scheme's qualifier list only if all of its type variables are among the variables being quantified for that binding.
- Generalized type variables behave as rigid at use sites until explicitly instantiated (Section 3.2).
- No generalization is performed inside arbitrary expression chains; only bindings that meet the value restriction are considered for schemes.

---

## 4. Constraint Generation

### 4.1 Expressions

Expression typing walks the AST inside a binding group and emits constraints into the current node of the constraint tree (Section 4.6).

- **Variable reference `x`**
  - Look up `x` in the environment. If it has a type scheme, **instantiate** it (Section 3.2), producing a mono type and wanted predicates at the current node.
  - If it is monomorphic, reuse its mono type directly.
  - The expression's type is the instantiated or mono type.

- **Function call `f(e0, e1, …, en)`**
  - Infer or instantiate the type of `f`, expecting a function type `(A0, A1, …, An) -> R`.
  - For each argument `ei`, infer its type `Ti` and emit an equality constraint `Ti == Ai`.
  - The call expression's type is `R`.
  - Any predicates arising from `f`'s scheme (via instantiation) become wanteds at the call site.

- **Method call `recv.m(e1, …, en)`**
  - Infer the type of `recv` as `Tr`.
  - Introduce a fresh meta `Trecv` for the logical receiver type expected by the method.
  - Emit a `Recv[Trecv, Tr]` wanted predicate to capture auto-ref/deref from `Tr` to `Trecv`.
  - Resolve the method to a trait method (e.g. desugaring to `T::m(recv, e1, …, en)`), which in turn generates:
    - A class predicate for the trait applied to the chosen receiver and type arguments.
    - Equality constraints for arguments and result, as in a normal function call.

- **Nilable literals `nil` and `some(e)`**
  - For `some(e)`:
    - Infer the type of `e` as `T`.
    - Give `some(e)` the type `nilable[T]` via an equality constraint tying the inner type to `T`.
  - For the bare literal `nil`:
    - Introduce a fresh meta `?a` and give `nil` the type `nilable[?a]`.
    - The meta `?a` must be resolved by surrounding constraints (e.g. assignment to a `nilable[int]` variable) or will remain ambiguous and be reported as such; there is no defaulting for `nil`.

- **Numeric literals**
  - A bare integer literal introduces a fresh meta `?a` for its type.
  - Emit a wanted predicate `Int[?a]` referring to the core `Int` trait: `trait Int['a] { default(int) }`.
  - Later, instance resolution and defaulting (Sections 6 and 8) will either fix `?a` via constraints or default it using `Int`'s `default(int)` marker.

- **Conditionals**
  - For `if cond { e_then } else { e_else }`:
    - Infer `cond` and constrain it to `bool` via equality.
    - Infer `e_then : T_then` and `e_else : T_else` and emit `T_then == T_else`.
    - The `if` expression's type is that common type.

### 4.2 Statements

Statements in Ray are primarily sequencing and bindings:

- Pure expression statements generate the same constraints as expressions and discard the resulting type.
- Binding statements `x = e` or `mut x = e` are handled as bindings (Section 4.3), with the expression `e` generating constraints and the name `x` being added to the environment for the remainder of the binding group.

### 4.3 Function definitions

Function definitions are the main source of binding groups:

- **Annotated functions**
  - Syntax examples:
    - `fn foo(x: T) -> U { ... }`
    - `fn foo['a](x: 'a) -> U { ... }`
    - `fn foo(x: 'a) -> U { ... }` (implicit generic `'a`).
  - The declared type is parsed into a scheme `forall['a..]. P => T`.
  - Annotated free functions still participate in binding-group analysis with neighboring bindings, but their declared schemes are treated as fixed: the solver does not infer new polymorphism for them, and their bodies are checked against their declared schemes.
  - At the binding-group root for `foo`:
    - **Skolemize** the scheme (Section 3.3), introducing skolems for `'a..` and adding `P` as givens.
    - Type-check the body against `T` under these givens, emitting equalities and additional wanteds.
  - No further generalization is performed for explicitly annotated items; their schemes are fixed by the annotation.

- **Unannotated free functions**
  - Unannotated functions participate in binding-group analysis and may be mutually recursive.
  - For each such function, introduce a fresh meta type for its full function type `(T0, …, Tn) -> R`.
  - Type-check the body, generating constraints relating parameter types, body result type, and usage sites.
  - After solving equalities for the group, attempt **value-restricted generalization** (Section 3.4) on each function:
    - If the function is a syntactic value and its unresolved metas are not fixed by outer constraints, quantify them to form a scheme.
    - Otherwise, leave it monomorphic.

- **Where-clauses and bounds**
  - Rust-style where-clauses and parameter bounds (e.g. `fn foo['a](x: 'a) where C['a, 'b] { ... }`) are desugared into class predicates added to the binding-group root as **givens**.
  - These givens are available to the goal solver when discharging wanteds inside the function body.

### 4.4 Trait and impl items

Traits and impls introduce and discharge class predicates:

- **Trait definitions**
  - Syntax example:
    `trait Foo['a, 'b, 'c] where C['a, 'b] { fn foo(self: 'a, b: 'b) -> 'c }`
  - A trait declaration does not itself generate constraints for a specific program point; it defines:
    - A predicate constructor `Foo['a, 'b, 'c]`.
    - Method signatures, which are treated as polymorphic schemes with an implicit `self`/receiver parameter.
    - Optional where-clause predicates (e.g. `C['a, 'b]`) that are logically required whenever `Foo` holds; these become additional givens in contexts where `Foo` is assumed (such as impls and uses of its methods).

- **Impl items and trait methods**
  - Impl headers introduce **givens** of the form `Foo[Recv, A1, …, An]` for all methods in the impl, plus any where-clause predicates.
  - Each trait method body is required to be fully annotated and forms a singleton binding group:
    - Skolemize the method's scheme using the impl's type parameters and trait givens.
    - Add the impl's trait predicate and where-clause predicates as givens at the method's root node.
    - Type-check the body against the skolemized signature, generating equalities and wanteds as usual.
  - No inference of additional polymorphism happens inside impl methods; they are checked against their declared types under the provided givens.

Method resolution for calls `recv.m(e1, …, en)` is layered on top of this:

- The surface syntax `recv.m(args)` is desugared, once types are known, to a trait-method call of the form `T::m(recv', args)` where:
  - `T` is the receiver type (or some trait object type) after applying `Recv` adjustments.
  - `recv'` is the adjusted receiver expression (after auto-ref/deref).
- The goal solver must ensure that there is a trait predicate `Foo[T, A1, …]` in scope (either as a given or via instance resolution) whose method set includes `m`. The evidence for that predicate is attached to the call site so the IR knows which method implementation to invoke.

### 4.5 Record construction & access

Record operations generate `HasField` constraints in a nominal way:

- **Struct construction `A { x: e1, y: e2 }` or `A { x, y: e2 }`**
  - The struct name `A` determines a nominal record type `A`.
  - For each field `f` in the literal, infer the type `Tf` of the corresponding expression.
  - From the struct declaration, the compiler knows the declared field type `DeclTy(A, f)`. Emit an equality `Tf == DeclTy(A, f)` to ensure the literal matches the struct's definition.
  - The overall expression is given type `A`. No structural row-polymorphism is performed; only the declared fields of `A` are allowed.

- **Field access `e.x`**
  - Infer the type of `e` as some nominal record type `R`.
  - From the declaration of `R`, look up the type `DeclTy(R, x)` of field `x`.
  - Emit a `HasField[R, "x", DeclTy(R, x)]` predicate at the access site and, if needed, an equality tying the access expression's type to `DeclTy(R, x)`.

Because records are nominal, `HasField` is essentially a way to thread field information through the constraint and instance machinery; it does not enable structural matching between unrelated record types.

### 4.6 Constraint tree structure and construction

Constraint generation organizes constraints into a tree of nodes that mirror the lexical and control-flow structure of a binding group:

- The root node corresponds to the binding group itself.
- Child nodes correspond to nested scopes: `if` branches, `match` arms, blocks, and pattern scopes.
- Each node stores:
  - A local typing environment (term and type bindings visible in that scope).
  - A set of **givens** (predicates and structural facts assumed to hold here).
  - A set of **wanteds** (constraints generated in this subtree).
- Conceptually, you can think of a node as:

  ```rust
  ConstraintNode {
    id: NodeId,
    parent: Option<NodeId>,
    children: Vec<NodeId>,
    env: TypeEnvId,
    givens: Vec<Predicate>,
    wanteds: Vec<Constraint>,
  }
  ```

Constraint-tree nodes are built during constraint generation by maintaining a stack of "current nodes":

- Initialize the root node for the binding group and push it onto a node stack.
- As the generator descends into the AST:
  - When entering a new scope (e.g. the body of an `if` branch, a block, or a pattern scope), create a fresh child node:
    - Link it to the current node as a child.
    - Seed its environment and givens from the parent (copy or share by reference, depending on implementation).
    - Push it onto the node stack and make it the current node.
  - When leaving that scope, pop the node stack to restore the parent as the current node.
- In practice, node creation and constraint emission happen in a single pass; we describe them separately here for clarity.

Pseudo-code, ignoring details of the AST:

```rust
fn build_constraint_tree(group: BindingGroup) -> ConstraintNode {
  let root = ConstraintNode::new_root(group);
  let stack = [root];
  walk(group.body, stack);
  return root;
}

fn walk(node: AstNode, stack: &mut Vec<ConstraintNode>) {
  let current = stack.last_mut();
  match node {
    Scope(body) => {
      let child = ConstraintNode::new_child(current);
      stack.push(child);
      for stmt in body { walk(stmt, stack); }
      stack.pop();
    }
    Expr(e) => generate_expr_constraints(e, current),
    Stmt(s) => generate_stmt_constraints(s, current, stack),
  }
}
```

---

## 5. Solving Architecture Overview

At a high level, Ray's type checker has three cooperating pieces:

- A **constraint generator** (Section 4) that walks the AST of a binding group, builds the constraint tree, and attaches equality and predicate constraints to the right nodes, without solving them.
- A single **unifier** (equality engine) that owns the meta-variable substitution and solves `t1 == t2`.
- A **term solver** that operates over the generated constraint tree, using the unifier to solve equality constraints and simplify types, but not performing instance resolution.
- A **goal solver** that works over the same tree and substitution, again using the unifier plus the instance environment to decide which predicates are solvable.

### 5.1 Term Solver (equality solving)
The term solver operates over the constraint tree produced by constraint generation (Section 4). Its job is to:

- Take all **equality constraints** `t1 == t2` attached to nodes in the tree.
- Use the global unifier to solve these equalities, updating the meta-variable substitution and simplifying types throughout the tree.
- Leave all predicate constraints (class, `HasField`, `Recv`) untouched for the goal solver.

Conceptually, the term solver is a first pass over the tree that resolves as many type equalities as possible before any reasoning about traits or instances happens.

One simple implementation strategy is:

- Maintain a worklist of equality constraints for the whole binding group.
- Iterate until no more equalities remain:
  - Pop an equality `t1 == t2` from the worklist.
  - Feed it to the unifier, updating the global substitution.
  - Apply the updated substitution to all types and constraints in the tree.

Pseudo-code sketch:

```rust
fn term_solve(root: &mut ConstraintNode, subst: &mut Subst) {
  let mut worklist = collect_equalities(root);
  while let Some((t1, t2)) = worklist.pop() {
    unify(t1, t2, subst);
    apply_subst_to_tree(root, subst);
  }
}
```

Here `collect_equalities` walks the tree and gathers all equality constraints, and `apply_subst_to_tree` rewrites all stored types and constraints under the current substitution. More incremental strategies are possible, but all should behave as if all equalities were solved before predicate constraints are considered.

### 5.2 Goal Solver
The goal solver operates on the constraint tree and substitution produced by the term solver. It runs after term processing for a binding group and conceptually performs a bottom-up pass over the constraint tree:

- **Node-level solving**
  - At each node, the solver considers:
    - The node's **givens** (including givens inherited from ancestors). These are predicates we assume hold in this scope and never try to solve; we only *use* them.
    - The node's **wanteds** (predicate constraints generated in this subtree; equalities were already handled by the term solver). These are obligations we must try to solve.
    - The global instance environment (Section 6).
  - It then:
    - Uses the current unifier substitution to simplify all types in givens and wanteds at this node.
    - Repeatedly scans the node's wanteds until no further progress is possible:
      - For each predicate wanted:
        - First tries to match it against **givens** (local + inherited). For class predicates this means unifying the wanted head with a given head (e.g. using `Lt['a, 'a]` to solve `Lt[?t0, ?t1]`), which may generate new equalities for the unifier.
        - If no given applies, tries **instance resolution** for class predicates (Section 6).
        - Uses nominal struct information for `HasField`.
        - Uses the auto-ref/deref rules for `Recv`.
      - Whenever a wanted is successfully solved, the solver:
        - Records **evidence** for that predicate (see Section 5.4).
        - Marks that progress has been made so it will re-scan remaining wanteds (since new equalities may unlock them).
      - Once a full scan yields no newly solved predicates and no new equalities, any remaining predicates at this node are treated as residuals.

- **Residuals and propagation**
  - Solving proceeds bottom-up:
    - Solve all children first and collect their residual predicates.
    - Treat those residuals as additional wanteds at the parent node.
  - Any predicates that cannot be solved at a node are propagated upward to its parent.
  - At the binding-group root, any remaining residuals that cannot be satisfied become errors (unsatisfied predicates or ambiguities).

This is the OutsideIn-inspired replacement for the old "Qualifier.Prove/Qualifier.Assume" constraints:

- What used to be `Assume` is now represented as givens attached to nodes in the constraint tree.
- What used to be `Prove` is now represented as wanteds that the goal solver attempts to discharge using instances and givens.

Pseudo-code sketch for the goal solver:

```rust
fn goal_solve(root: &mut ConstraintNode, subst: &mut Subst) -> Vec<Constraint> {
  let inherited_givens = Vec::new();
  solve_node(root, &inherited_givens, subst)
}

fn solve_node(
  node: &mut ConstraintNode,
  inherited_givens: &Vec<Predicate>,
  subst: &mut Subst,
) -> Vec<Constraint> {
  // 1. Combine inherited givens with this node's own givens.
  let mut all_givens = inherited_givens.clone();
  all_givens.extend(node.givens.iter().cloned());

  // 2. Solve children first; propagate their residuals into this node.
  let mut worklist = Vec::new();
  for child in node.children.iter_mut() {
    let child_residuals = solve_node(child, &all_givens, subst);
    worklist.extend(child_residuals);
  }

  // 3. Add this node's own predicate wanteds.
  for c in node.wanteds.iter() {
    if let Constraint::Predicate(p) = c {
      worklist.push(Constraint::Predicate(p.clone()));
    }
  }

  // 4. Process the worklist to a fixpoint.
  let mut residuals = Vec::new();
  let mut changed = true;
  while changed {
    changed = false;
    let mut next_worklist = Vec::new();
  while let Some(c) = worklist.pop() {
    match c {
      Constraint::Predicate(p) => {
        // Simplify types under the current substitution.
        let p = subst.apply_predicate(p);
        if solve_predicate(&p, &all_givens, subst) {
          // Solved: record evidence inside solve_predicate and keep going.
          changed = true;
        } else {
          // Not yet solvable; carry it forward.
          next_worklist.push(Constraint::Predicate(p));
          }
        }
        // Equalities should have been handled by term_solve already.
        Constraint::Equality(_, _) => next_worklist.push(c),
      }
    }
    worklist = next_worklist;
  }

  residuals.extend(worklist);
  residuals
}
```

Here `solve_predicate` encapsulates the logic for class predicates, `HasField`, and `Recv`:

```rust
fn solve_predicate(p: &Predicate, givens: &Vec<Predicate>, subst: &mut Subst) -> bool {
  match p {
    Predicate::ClassPred(class) => solve_class_predicate(class, givens, subst),
    Predicate::HasFieldPred(hf) => solve_has_field(hf, subst),
    Predicate::RecvPred(rv) => solve_recv(rv, subst),
  }
}
```

- `solve_class_predicate` first tries to match `p` against `givens` (deriving equalities via unification where possible), and if that fails, falls back to instance resolution (Section 6).
- `solve_has_field` consults nominal struct metadata to check that the field exists on the declared record type and returns the field type, updating metas via the unifier as needed. Users cannot define new `HasField` behaviors; they are derived solely from struct declarations.
- `solve_recv` explores a small, Rust-like set of auto-ref/deref adjustments between `ExprTy` and `RecvTy`, and uses unification to relate the receiver type to the method's `self` parameter. If there is no legal adjustment within these rules, the `Recv` predicate cannot be discharged and remains as an unsolved wanted; if it survives to the binding-group root, it is reported as a type error just like any other unsatisfied predicate. The "improvement" aspect of `Recv` is that it does not introduce new obligations beyond equalities and the chosen adjustment: it does not generate additional class predicates.

### 5.3 Interaction Between Solvers
Putting the pieces together, solving for a binding group proceeds in phases:

At the top level, the driver determines binding groups (Section 1.3), then runs the following pipeline for each group:

```rust
fn typecheck_binding_group(group: BindingGroup, global_env: &mut GlobalEnv) {
  // 1. Generate constraints and tree from the AST.
  let mut root = generate_constraints(group);          // Section 4

  // 2. Solve equalities.
  let mut subst = Subst::empty();
  term_solve(&mut root, &mut subst);                   // Section 5.1

  // 3. Solve predicates.
  let mut residuals = goal_solve(&mut root, &mut subst);   // Section 5.2

  // 4. Apply defaulting to remaining metas and predicates.
  default_residuals(&mut residuals, &mut subst);       // Section 8

  // 5. Generalize successful bindings and update the global environment.
  generalize_group(&group, global_env, &subst, &residuals); // Section 3.4

  // 6. Report any remaining residuals as errors.
  report_errors(residuals, &mut global_env.type_info); // Section 9
}
```

A `BindingGroup` here is the syntactic group of mutually recursive bindings and items identified by earlier analysis; `GlobalEnv` is the global typing environment mapping names to their (possibly polymorphic) types, plus accumulated type-system information.

In more detail, each phase corresponds to the following operations:

1. **Constraint generation and tree construction (Section 4)**
   - Walk the binding group, build the constraint tree, and attach equality and predicate constraints to nodes.

   ```rust
   fn generate_constraints(group: BindingGroup) -> ConstraintNode {
     let mut root = ConstraintNode::new_root(group);
     let mut stack = vec![&mut root];
     walk_ast(group.body, &mut stack);
     root
   }
   ```

2. **Term solving (equalities, term solver, Section 5.1)**
   - Run the term solver over the tree to solve all equality constraints using the unifier, simplifying types everywhere.

   ```rust
   fn term_solve_group(root: &mut ConstraintNode) -> Subst {
     let mut subst = Subst::empty();
     term_solve(root, &mut subst); // see Section 5.1
     subst
   }
   ```

3. **Predicate solving (goal solver, Section 5.2)**
   - Traverse the constraint tree bottom-up. At each node:
     - Use the current substitution to simplify types in givens and wanteds.
     - For each predicate wanted, attempt to solve it using the node's givens and the instance environment; any equalities arising from instance heads or contexts are fed back to the unifier.
     - Collect any predicates that remain unsolved as residuals and propagate them upward.

4. **Defaulting (Section 8)**
   - After predicate solving, examine metas that remain constrained only by defaultable predicates (e.g. `Int[?a]`, `Float[?a]`).
   - For each such meta, attempt to choose a default type according to the rules in Sections 8.2–8.3, record the equality in the substitution, and then *re-run predicate solving on the residual predicates* under the updated substitution. This may turn previously unsolved or ambiguous predicates into solvable ones.

5. **Generalization at the binding-group root (Section 3.4)**
   - After predicate solving and defaulting, inspect the types of bindings in the group.
   - For each binding that satisfies the value restriction, quantify over remaining unsolved metas to form a type scheme; others remain monomorphic.

   ```rust
   fn generalize_group(
     group: &BindingGroup,
     global_env: &mut GlobalEnv,
     subst: &Subst,
     residuals: &Vec<Constraint>,
   ) {
     for binding in group.bindings.iter() {
       // Skip bindings that have residual errors; they do not generalize.
       if has_residual_for(binding, residuals) {
         continue;
       }
       let ty = subst.apply(binding.inferred_ty.clone());
       if is_value(binding.expr) && can_generalize(&ty) {
         let scheme = generalize(ty);
         global_env.insert_scheme(binding.name.clone(), scheme);
       } else {
         let scheme = Scheme::mono(ty);
         global_env.insert_scheme(binding.name.clone(), scheme);
       }
     }
   }
   ```

6. **Error reporting (Section 9)**
   - Any unsolved predicates or ambiguous constraints at the binding-group root become type errors.

   ```rust
   fn report_errors(residuals: Vec<Constraint>, info: &mut TypeSystemInfo) {
     for c in residuals {
       match c {
         Constraint::Predicate(p) => info.missing_predicate(&p),
         Constraint::Equality(t1, t2) => info.equality_type_pair(&t1, &t2),
       }
     }
   }
   ```

Together, these phases ensure that each binding group is solved in isolation with a clear, structured flow of information: constraint generation builds the tree, the term solver resolves equalities, the goal solver resolves predicates using instances and givens, generalization wraps up the remaining polymorphism, and any unresolved obligations are surfaced as errors.

### 5.4 Evidence representation and threading

Evidence is the internal witness that a predicate has been solved. The goal solver produces evidence; later compilation stages consume it when deciding how to implement trait methods, field accesses, and receiver adjustments.

- **What evidence represents**
  - For a class predicate `C[Recv, A1, …, An]`, evidence identifies:
    - The chosen instance (e.g. `impl_id`), and
    - Any associated runtime representation (such as a vtable, set of function pointers, or dictionary) later phases use to implement trait methods.
  - For `HasField[RecordTy, FieldName, FieldTy]`, evidence describes how to project the field at runtime:
    - Typically an offset, index, or a specialized projection function.
  - For `Recv[RecvTy, ExprTy]`, evidence is the concrete sequence of auto-ref/deref steps (e.g. "take a ref", "deref once") that must be applied to the expression to obtain the receiver.

- **Evidence IDs and storage**
  - The solver treats evidence in terms of opaque IDs:

    ```rust
    struct EvidenceId(u32);

    enum Evidence {
      ClassEvidence { instance_id: InstanceId },
      HasFieldEvidence { field_index: u32 },
      RecvEvidence { steps: Vec<RecvStep> },
    }

    struct EvidenceEnv {
      map: HashMap<EvidenceId, Evidence>,
    }
    ```

  - `InstanceId` and `RecvStep` are backend-defined; the type checker does not commit to a particular runtime layout, only to producing a consistent mapping from `Predicate` to `EvidenceId` and `Evidence`.

- **Where evidence is produced**
  - Inside `solve_predicate` (and its helpers), whenever a predicate is successfully discharged, the solver:
    - Allocates a fresh `EvidenceId`.
    - Constructs an `Evidence` value describing how that predicate was solved.
    - Inserts it into a shared `EvidenceEnv` carried alongside the constraint tree.
  - The solver also attaches the `EvidenceId` to the AST node that required the predicate:
    - During type checking on the AST, evidence is associated with **AST node IDs**:

      ```rust
      type AstExprId = u32;

      struct EvidenceMaps {
        expr_evidence: HashMap<AstExprId, EvidenceId>,
        // similar maps can exist for patterns/statements if needed
      }
      ```

    - Later compilation stages that transform or analyze the AST:
      - Walk the AST, carrying over `EvidenceId`s from `EvidenceMaps` to their own representation of call sites and field accesses.
      - For a method call `x.m(...)`, the node representing the call records the evidence for the trait bound used to resolve `m`.
      - For `e.x`, the node representing the projection records the evidence for the relevant `HasField`.
      - For receiver adjustments, the call site records the `Recv` evidence so coercions can be emitted.

- **How evidence is consumed**
  - Later compiler phases consult the `EvidenceEnv` and the `EvidenceId` annotations on nodes to:
    - Pick the right method implementation or vtable for trait calls.
    - Generate field access code using the offset/index from `HasFieldEvidence`.
    - Insert the appropriate load/store/deref/ref instructions described by `RecvEvidence`.
  - Because evidence is opaque to the type system, later stages are free to change their internal representation (e.g. switch from dictionaries to direct monomorphization) as long as they preserve the mapping from predicates to correct runtime behavior.

---

## 6. Instance Resolution

### 6.1 Instance Scheme Representation

Each `impl` declaration introduces an *instance scheme* for a trait predicate:

  - **Syntax examples**
    - `impl Foo[Recv, A, B] where P, Q, ...`
    - `impl Index[list['a], 'a, uint]`
- **Internal representation**
  - A set of universally quantified type variables `'a..` from the impl header.
  - A *head predicate* of the form `C[Recv, A1, …, An]` describing where the instance applies.
  - A list of *context predicates* `P, Q, …` (from where-clauses and trait-level requirements) that must hold whenever this instance is used.

Instances are stored in a global instance environment indexed by their head trait name and arity.

Pseudo-code sketch:

```rust
struct Instance {
  id: InstanceId,
  vars: Vec<TyVar>,        // ['a, 'b, ...]
  head: Predicate,         // e.g. Add[Recv, A, B]
  context: Vec<Predicate>, // where-clauses and trait-level requirements
}

struct InstanceEnv {
  map: HashMap<TraitName, Vec<Instance>>,
}

fn register_instance(env: &mut InstanceEnv, inst: Instance) {
  env.map.entry(inst.head.trait_name())
    .or_default()
    .push(inst);
}

fn lookup_instances<'a>(
  env: &'a InstanceEnv,
  trait_name: &TraitName,
) -> impl Iterator<Item = &'a Instance> {
  env.map.get(trait_name).into_iter().flatten()
}
```

The solver builds this `InstanceEnv` during module loading, before any binding groups are type-checked.

### 6.2 Matching algorithm

Given a wanted class predicate `W = C[T0, T1, …, Tn]` at some node, instance resolution proceeds as follows:

1. **Collect candidates**
   - Look up all instance schemes for `C` with compatible arity.
2. **Head unification**
   - For each candidate instance with head `C[H0, H1, …, Hn]`, attempt to unify `H0..Hn` with `T0..Tn`, treating the instance's quantified variables as fresh metas.
   - If unification succeeds, record the resulting substitution as a candidate match; if it fails, discard the instance.
3. **Viable candidates and context obligations**
   - For each successful candidate, instantiate its context predicates `P, Q, …` under the unifier and emit them as new wanted predicates at the same node (or an appropriate child), to be solved by the goal solver. This applies only to **class predicates**; `HasField` and `Recv` are not resolved via user-visible instances.
   - A candidate is considered **viable** if:
     - Its head unifies with the wanted predicate (as above), and
     - Its substitution does **not** bind any rigid/skolem variables (i.e., all bindings are for flexible metas), and
     - It is not rejected by any additional consistency checks (e.g., future directives or coherence rules).
4. **Selection**
   - If there is exactly one **viable** candidate after this filtering, select it and use its context obligations plus evidence as the solution for `W`.
   - If there are no viable candidates, `W` remains unsolved at this node and is deferred as a residual predicate; it may eventually cause an error at the binding-group root.
   - If there are multiple viable candidates, treat `W` as ambiguous at this node and defer it; if it remains unsolved at the root, it becomes an `AmbiguousPredicate` error.

The result of successful instance resolution is both:
- A proof term/evidence for `W` (used later by code generation).
- Additional wanted predicates arising from the instance context.

Pseudo-code sketch for class predicates:

```rust
fn solve_class_predicate(
  wanted: &ClassPredicate,
  givens: &Vec<Predicate>,
  subst: &mut Subst,
  inst_env: &InstanceEnv,
  evidence_env: &mut EvidenceEnv,
) -> bool {
  // 1. Try to discharge from givens first.
  if let Some(ev_id) = solve_from_givens(wanted, givens, subst, evidence_env) {
    attach_evidence(wanted, ev_id);
    return true;
  }

  // 2. Fallback to instances.
  let candidates = lookup_instances(inst_env, &wanted.trait_name());
  let mut matches = Vec::new();
  for inst in candidates {
    if let Some(inst_subst) = match_instance_head(inst, wanted, subst) {
      matches.push((inst, inst_subst));
    }
  }

  match matches.len() {
    0 => false, // no instance
    1 => {
      let (inst, inst_subst) = matches.into_iter().next().unwrap();
      subst.compose(inst_subst);
      // emit context predicates as new wanteds handled by the goal solver
      emit_context_wanteds(inst, subst);
      let ev_id = evidence_env.fresh_class_evidence(inst.id);
      attach_evidence(wanted, ev_id);
      true
    }
    _ => {
      // overlapping/ambiguous instances
      false
    }
  }
}
```

### 6.3 Overlap detection

Two instance schemes for the same trait are *overlapping* if there exists a substitution for their quantified variables that makes their heads unify.

- Example of *non-overlapping* instances:
  - `impl Add[rawptr['a], uint, rawptr['a]]`
  - `impl Add[uint, uint, uint]`
  These are disjoint because their receiver positions (`rawptr['a]` vs `uint`) can never unify.

Ray's instance resolution requires that, for any concrete wanted predicate, there is at most one most specific applicable instance:

- If multiple matching instances exist and neither is strictly more specific than the others (according to head unification), the program is rejected as having overlapping/ambiguous instances.
- Specialization (choosing a more specific instance in the presence of a more general one) is not modeled in this spec and would be treated as a future extension.

### 6.4 Coherence rules

This specification does not currently impose Rust-style orphan rules. In particular:

- An `impl` may be written for any trait/type combination, regardless of where the trait or type are defined.
- Coherence is enforced *per compilation unit* by rejecting overlapping instances as described in Section 6.3.

Cross-crate coherence and more restrictive orphan rules may be introduced in the future, but are out of scope for this document. For now, contributors should assume that all visible instances participate in overlap checking, and that adding a new instance may cause existing code to become ambiguous.

---

## 7. Multi-Parameter Type Classes

### 7.1 Variance / sensitivity considerations
Multi-parameter traits in Ray are Rust-flavored:

- The **first parameter is always the receiver type** and is the one involved in method resolution and `Recv` adjustments.
- All remaining parameters are plain type arguments with no special roles imposed by the type system (no designated "output" positions, no implicit input/output variance).
- The type system does **not** assume any implicit dependencies or functional dependencies between parameters. Any relationships must be expressed by reusing the same type variable in multiple positions or by explicit qualifiers.

Associated types are not part of the current core design, but the receiver-first convention and explicit parameter list leave room to add them in the future without changing the basic constraint model.

### 7.2 Schema equality relations

Equalities between trait parameters are derived only from how a trait predicate appears in a particular context, not from the trait definition alone:

- Using the same type variable in multiple positions expresses an equality requirement locally. For example, a qualifier `forall t. C[t, t]` tells the solver that, within that qualified context, the corresponding parameters of `C` are equal.
- Trait where-clauses (on traits, impls, or functions) that mention a predicate like `C['a, 'a]` introduce the same local equality wherever those clauses are assumed as givens.

In practice, equalities between *different* metas arise when matching wanteds against such givens. For example, in:

```rust
fn lt(a: 'a) -> bool where Int['a] Lt['a, 'a] => a < 0
```

- The parameter has type `?t0` (instantiation of `'a`), and the literal `0` has type `?t1`.
- Constraint generation produces:
  - A given `Lt['a, 'a]`, instantiated to `Lt[?t0, ?t0]` at this use site.
  - A wanted `Lt[?t0, ?t1]` for `a < 0`.
- When the goal solver uses the given `Lt[?t0, ?t0]` to solve the wanted `Lt[?t0, ?t1]`, it unifies their heads and learns the equality `?t1 == ?t0`. That equality is then fed to the unifier, effectively enforcing that both arguments of the `Lt` predicate share the same type in this context.

Operationally:

- When a qualifier or where-clause introduces a predicate such as `C[X, X]` at a node, the important fact is that both class parameters are instantiated with the same type variable `X` in that scope. The solver does not manufacture an extra `X == X` constraint; the shared variable is already the equality.
- These locally shared variables may influence unification and instance selection within that node and its children, but they do not change the global meaning of `C` or introduce any global fundep-like behavior. Outside the scope where the qualifier holds, no such relationship is assumed.

### 7.3 Expected solver behavior without fundeps

Given the lack of user-visible functional dependencies and injectivity, the solver must follow these guidelines:

- **No inference from class definitions alone**
  The presence of a trait `C[Recv, A, B]` does not, by itself, allow the solver to infer any relationship between `A` and `B`. Only explicit reuse of variables (e.g. `C['a, 'a]`) or external equalities may relate them.

- **Local improvement only**
  Any equalities derived from how predicates appear (e.g. from qualifiers, where-clauses, or specific instance heads) are scoped to the constraint-tree node where they are introduced. They may be used to:
  - Simplify types and unify metas within that node.
  - Prefer more specific instances during resolution when heads become more concrete under these equalities.
  But they must not leak out and alter constraints in unrelated parts of the program.

- **Ambiguity in the absence of clear equalities**
  If resolving a multi-parameter trait would require choosing between multiple incomparable typings for secondary parameters (those after the receiver) and there is no local schema-based equality or annotation to decide, the solver should treat the situation as ambiguous and require an explicit type annotation rather than guessing.

This disciplined behavior keeps multi-parameter traits usable and expressive while avoiding the complexity of full Haskell-style fundeps or type families. It also aligns with Ray's goal of predictable local reasoning: all non-trivial relationships between trait parameters are visible at their use sites or in explicit where-clauses.

---

## 8. Defaulting

### 8.1 When defaulting runs
Defaulting occurs late in the solving process, after:
- Term solving and unification have run for each binding group.
- The goal solver has attempted to resolve all class predicates using instances and givens.

At this point, some residual class predicates at the binding-group root may still mention flexible type variables whose concrete types have not been fixed. Defaulting is allowed only to resolve such ambiguities; it must not change which programs are considered well-typed.

### 8.2 Defaultable predicates and type-variable classes

Traits may opt into defaulting by declaring a preferred concrete type:

- Example core traits:
  - `trait Int['a] { default(int) }`
  - `trait Float['a] { default(f32) }`

For each trait `C` with a `default(T_default)` marker:

- `T_default` is a candidate default type for the **receiver** type variable in predicates `C[α, …]` that survive to the binding-group root.
- Defaulting is described in terms of **type-variable classes**:
  - After unification, each type variable belongs to an equivalence class `α` (all metas unified together).
  - A class `α` is *flexible* if it is represented by a meta variable that is not unified with a rigid or skolem and is not yet fixed by an equality.
- Residual predicates are grouped into **clusters** of mutually-dependent type-variable classes; defaulting considers clusters that contain at least one class appearing as the receiver of a trait with `default(T_default)`.

We also talk about when a type-variable class `α` *will be generalized* in this binding group:

- At the group root, after term solving, goal solving, and defaulting, each binding `x` that is `eligible_for_generalization(x)` (Section 3.4) has a final monomorphic type `Ty_x`.
- Let `F_x` be the set of flexible metas that occur free in `Ty_x`; these are the variables that would be generalized to form `forall[F_x]. P_x => Ty_x` for that binding.
- A class `α` *will be generalized* if it belongs to some `F_x` for a binding `x` in this group.
- Such classes must not be defaulted, because doing so would silently turn a potentially polymorphic binding into a monomorphic one by choosing a concrete default type instead of quantifying.

Algorithmically, this check can be expressed as a helper:

```rust
fn will_be_generalized(alpha: TyVarId, group: &BindingGroupRoot) -> bool {
  for binding in group.bindings() {
    if !eligible_for_generalization(binding) {
      continue;
    }
    let ty_x = binding.type_after_solving(); // mono type with metas
    if ty_x.contains_flexible_meta(alpha) {
      return true;
    }
  }
  false
}
```

Here `group.bindings()` iterates all bindings in the binding group, `eligible_for_generalization` is as defined in Section 3.4, and `contains_flexible_meta` checks whether `alpha` appears as a flexible meta in `Ty_x` under the current substitution.

Intuitively:

- Defaulting is triggered **by residual predicates**, not by metas in isolation.
- Other predicates that mention the same type-variable class `α` are allowed; they do not prevent defaulting a priori, but they may veto a particular default choice if it would make the cluster of predicates involving `α` unsatisfiable.

More concretely, defaulting uses a two-step view of defaultable classes and their clusters:

1. **Selecting defaultable classes**  
   Scan the residual predicates at the group root. For each predicate `C[args...]` where `C` has `default(T_default)` and the receiver argument is a type-variable class `α`, mark `α` as *defaultable*.

2. **Clustering by shared predicates**  
   Build an undirected graph over defaultable classes where an edge connects any two classes that co-occur in a residual predicate. Each connected component is a *cluster*. For a cluster `C`, define `preds_C` to be all residual predicates that mention any class in `C`. A candidate default assignment is only accepted if `preds_C` remains solvable.

### 8.3 Defaulting algorithm

Conceptually, the defaulting pass works over the residual predicates at the binding-group root and records its decisions in a small log:

```rust
enum DefaultingOutcomeKind {
  Succeeded,
  RejectedRigid,      // α unified with a rigid/skolem; cannot be defaulted
  RejectedPoly,       // α will be generalized into a forall-variable; cannot be defaulted
  RejectedUnsat {     // α == T_default would break other predicates
    blocking_preds: Vec<Predicate>,
  },
  RejectedAmbiguous { // multiple viable defaults; do not guess
    candidates: Vec<Ty>,
  },
}

struct DefaultingOutcome {
  var: TyVarId,          // representative of type-variable class α
  default_ty: Ty,        // the T_default we considered
  kind: DefaultingOutcomeKind,
}

struct DefaultingLog {
  entries: Vec<DefaultingOutcome>,
}
```

A high-level algorithm for defaulting at a group root:

```rust
fn default_residuals(
  root: &ConstraintNode,
  subst: &mut Subst,
  instances: &InstanceEnv,
  log: &mut DefaultingLog,
) {
  let residuals = root.residual_predicates();

  // Build clusters of defaultable classes connected by shared predicates.
  let clusters: Vec<(Vec<TyVarId>, Vec<Predicate>)> =
    build_defaulting_clusters(&residuals, subst);

  for (cluster, preds_cluster) in clusters {
    // Skip clusters containing any class that is rigid or will be generalized.
    if cluster.iter().any(|alpha| !is_flexible(*alpha, subst)) {
      for alpha in cluster {
        log.entries.push(DefaultingOutcome {
          var: alpha,
          default_ty: inferred_default_ty_for(alpha, &preds_cluster),
          kind: DefaultingOutcomeKind::RejectedRigid,
        });
      }
      continue;
    }
    if cluster.iter().any(|alpha| will_be_generalized(*alpha, root)) {
      for alpha in cluster {
        log.entries.push(DefaultingOutcome {
          var: alpha,
          default_ty: inferred_default_ty_for(alpha, &preds_cluster),
          kind: DefaultingOutcomeKind::RejectedPoly,
        });
      }
      continue;
    }

    // Collect candidates per class and consider joint assignments.
    let candidates = default_candidates_for_cluster(&cluster, &preds_cluster);
    if candidates.is_empty() {
      continue;
    }

    let mut viable = Vec::new();
    for assignment in candidates {
      // Try { α_i == T_i } without committing yet.
      let mut subst_try = subst.clone();
      for (alpha, ty) in &assignment {
        subst_try.bind(*alpha, ty.clone());
      }

      if solve_predicates_for_class(&preds_cluster, &mut subst_try, instances).is_ok() {
        viable.push(assignment);
      } else {
        for (alpha, ty) in assignment {
          log.entries.push(DefaultingOutcome {
            var: alpha,
            default_ty: ty,
            kind: DefaultingOutcomeKind::RejectedUnsat {
              blocking_preds: preds_cluster.clone(),
            },
          });
        }
      }
    }

    match viable.len() {
      0 => { /* no viable defaults; leave cluster undecided */ }
      1 => {
        let assignment = viable.into_iter().next().unwrap();
        for (alpha, ty) in assignment {
          subst.bind(alpha, ty.clone());
          log.entries.push(DefaultingOutcome {
            var: alpha,
            default_ty: ty,
            kind: DefaultingOutcomeKind::Succeeded,
          });
        }
      }
      _ => {
        for alpha in cluster {
          log.entries.push(DefaultingOutcome {
            var: alpha,
            default_ty: Ty::Unknown, // implementation-specific placeholder
            kind: DefaultingOutcomeKind::RejectedAmbiguous {
              candidates: viable
                .iter()
                .filter_map(|assignment| assignment.iter().find(|(a, _)| *a == alpha))
                .map(|(_, ty)| ty.clone())
                .collect(),
            },
          });
        }
      }
    }
  }
}
```

Notes:

- This algorithm is phrased in terms of **predicates**, not raw meta variables:
- It first finds the type-variable classes `α` that appear in residual predicates from traits with `default(T_default)`.
  - It then groups those classes into clusters based on shared predicates, and checks candidate defaults per cluster.
- Other constraints (including non-defaultable traits) do not prevent defaulting:
  - They only veto a particular default `T_default` if adding `α == T_default` would make the cluster unsatisfiable.
- Only flexible, non-generalized type-variable classes are considered:
  - A variable unified with a skolem (such as the parameter type in `fn lt_zero(a: 'a) -> bool where Int['a], Lt['a, 'a] => a < 0`) is not defaulted.
  - Variables that will be quantified into a `forall` scheme are not defaulted.

### 8.4 Interactions with goal solving and errors

Defaulting is a final pass over the residual constraint set at the binding-group root:

- It may add equalities of the form `α == T_default` for some flexible, non-generalized type-variable classes `α`.
- After committing these equalities to the main substitution, the solver re-runs a lightweight goal-solving step for the affected predicates to propagate the effects.

If no viable default exists for a class `α`, or if multiple defaults are viable and incomparable, `α` is left undecided. Any predicates that still mention `α` contribute to ambiguity errors (Section 9.4). The `DefaultingLog` is carried alongside `TypeSystemInfo` so that diagnostics can say things like:

- "`'a` in `Int['a]` could be defaulted to `int`, but that choice conflicts with the predicates `Eq['a]` and `Ord['a]`."
- "`?0` appears only in defaultable predicates, but both `Int['?0]` and `Float['?0]` are viable; add an annotation to disambiguate."

---

## 9. Error Model

Ray's type checker reports errors using a rich `TypeSystemInfo` structure (see `crates/ray-typing/src/info.rs`), which records both the primary error and a trail of contributing facts (predicates, schemes, directives, and source spans). This section describes the conceptual categories of errors and how they arise from the solving architecture.

### 9.1 Term-level errors

Term-level errors come from failed equality constraints and misuses of term constructs:

- **Type mismatch (equality failure)**
  - Source: an equality wanted `t1 == t2` that the unifier cannot satisfy (e.g. trying to unify `int` with `bool`, or `(T0, T1) -> U` with `(V0,) -> W`).
  - Reporting: record an `EqualityTypePair(t1, t2)` in `TypeSystemInfo`, along with the relevant source spans for both sides.

- **Not-a-function / arity mismatch**
  - Source: expecting a function type `(A0, …, An) -> R` but inferring a non-function type, or a function with different arity.
  - Reporting: also treated as a failed equality between the inferred type and the expected function type, resulting in `EqualityTypePair`.

- **Illegal receiver / field access**
  - Source: `Recv` or `HasField` constraints that cannot be satisfied because the base type is not a valid receiver or record type.
  - Reporting: these ultimately degrade to a combination of missing/unsatisfied predicates (Section 9.2) and equality failures describing the expected shape.

In all cases, term-level errors originate from equality or structural constraints attached to a specific node in the constraint tree; the error carries enough `TypeSystemInfo` to point back to the expression that generated the failing constraint.

### 9.2 Predicate unsatisfied errors

Predicate errors arise when the goal solver cannot discharge a class, `HasField`, or `Recv` predicate:

- **Missing predicate (context requirement not satisfied)**
  - Source: a **required** predicate is not present in a context where it must appear. Typical cases:
    - A function or method signature requires a predicate in its where-clause, but the caller's context does not provide it.
    - Other higher-level rules demand that a particular predicate be in the given set for a scope, and it is absent.
  - Reporting: record `MissingPredicate(P)` in `TypeSystemInfo`, where `P` is the required predicate. `ParentPredicate` and `PredicateArisingFrom` entries can be used to show where the requirement came from.

- **No instance / unsolved predicate at group root**
  - Source: after goal solving and defaulting, a wanted predicate `P` (e.g. `C[T0, …, Tn]`, `HasField[R, "x", T]`, `Recv[RecvTy, ExprTy]`) remains in the residual set at the binding-group root because:
    - No instance matches, or
    - An instance's context predicates cannot themselves be satisfied.
  - Reporting: record `UnsolvedPredicate(P, info)` where `info` is the accumulated `TypeSystemInfo` from the derivation of `P`. This is distinct from `MissingPredicate`: here the solver *tried* to solve `P` using givens and instances but failed to find a matching instance or satisfy its context.

Predicate errors are always attached to the node where the obligation was last active; the corresponding `TypeSystemInfo` records how the predicate arose (e.g. from an instance context, where-clause, or method call).

### 9.3 Skolem escape errors

Skolem escape errors detect violations of polymorphic scoping:

- **Source**
  - During skolemization (Section 3.3), the solver introduces skolems for quantified variables and tags them with a scope.
  - If unification ever requires a skolem to unify with a type that would let it escape its scope (for example, trying to store a reference to a skolem-parameterized value in a longer-lived place), the solver must reject the program.

- **Reporting**
  - Record `EscapedSkolems([s1, …, sn])` in `TypeSystemInfo`, listing the skolems that attempted to escape.
  - Attach the relevant source spans for the original polymorphic binding and the use site that caused the escape.

This error category enforces that generalized type variables cannot be captured by longer-lived contexts, preserving soundness of polymorphism.

### 9.4 Ambiguity errors

Ambiguity errors arise when the solver cannot uniquely determine a type or instance even though some solutions exist:

- **Ambiguous predicate**
  - Source: a predicate `P` for which multiple incomparable instances match (Section 6.3), or for which solving would require choosing among several possible types for some meta variable without sufficient information.
  - Reporting: record `AmbiguousPredicate(P)` in `TypeSystemInfo`, possibly with additional `PredicateArisingFrom` entries to show where competing obligations came from.

- **Defaulting failure**
  - Source: after defaulting (Section 8), some residual predicates still mention flexible, non-generalized type-variable classes that:
    - Had at least one trait with `default(T_default)` in their predicate cluster, but no candidate `T_default` was compatible with all predicates (see `RejectedUnsat` in `DefaultingLog`), or
    - Had more than one viable default candidate and the solver refused to guess (see `RejectedAmbiguous` in `DefaultingLog`).
  - Reporting: treat these as ambiguous predicates as well, since the solver refuses to guess. Where helpful, include information from the `DefaultingLog`, for example:
    - "`'a` in `Int['a]` could have been defaulted to `int`, but that choice conflicts with `Eq['a]`."
    - "`?0` has both `Int['?0]` and `Float['?0]` as viable defaults; add an annotation."

Ambiguity is reported at the binding-group root, since it reflects an inherent under-specification of the program rather than a local mismatch. The associated `TypeSystemInfo` helps contributors and users see which uses and constraints contributed to the ambiguity.

---

## Appendix A: Algorithmic Typing Rules

We use judgments of the form:

```text
Γ ⊢ e ⇝ (T, C)
```

to mean: under type environment `Γ`, expression `e` has (inferred) type `T` and generates a set of constraints `C` (equalities and predicates) to be attached to the current constraint-tree node.

### A.1 Basic Expressions

**Variables**

If `Γ(x) = σ` where `σ` is a type scheme:

```text
Γ ⊢ x ⇝ (T, C)
```

where:

- `(P, T) = instantiate(σ)` (Section 3.2), producing a mono type `T` and predicates `P`.
- `C = P` (predicates become wanteds at this node).

If `Γ(x) = T` where `T` is monomorphic:

```text
Γ ⊢ x ⇝ (T, ∅)
```

**Integer literals**

For an integer literal `n`:

```text
Γ ⊢ n ⇝ (?a, { Int[?a] })
```

where:

- `?a` is a fresh meta variable for the literal's type.
- `Int[?a]` is a wanted predicate for the `Int` trait (Section 8).

**Float literals**

Similarly, for a float literal `f`:

```text
Γ ⊢ f ⇝ (?a, { Float[?a] })
```

where `?a` is fresh and `Float[?a]` is a wanted predicate.

**Other literals**

For non-overloaded primitive literals:

- String literal `"s"`:

  ```text
  Γ ⊢ "s" ⇝ (string, ∅)
  ```

- Character literal `'c'`:

  ```text
  Γ ⊢ 'c' ⇝ (char, ∅)
  ```

- Boolean literals `true` and `false`:

  ```text
  Γ ⊢ true ⇝ (bool, ∅)
  Γ ⊢ false ⇝ (bool, ∅)
  ```

**Nilable literals**

For `some(e)`:

```text
Γ ⊢ e ⇝ (T, C)
-------------------------------
Γ ⊢ some(e) ⇝ (nilable[T], C)
```

For the bare literal `nil`:

```text
Γ ⊢ nil ⇝ (nilable[?a], ∅)
```

where `?a` is a fresh meta; its concrete type must be determined by surrounding constraints or will be reported as ambiguous.

**Function calls**

For a function call `f(e0, …, en)`:

```text
Γ ⊢ f ⇝ (Tf, Cf)
Γ ⊢ e0 ⇝ (T0, C0)   …   Γ ⊢ en ⇝ (Tn, Cn)
Tf ≡ (A0, …, An) -> R
-------------------------------------------------
Γ ⊢ f(e0, …, en) ⇝ (R, Cf ∪ C0 ∪ … ∪ Cn ∪ { T0 == A0, …, Tn == An })
```

where:

- `Tf ≡ (A0, …, An) -> R` means `Tf` must unify with a function type with argument types `A0..An` and result type `R`; this introduces equalities `Tf == (A0, …, An) -> R` and `Ti == Ai` which the term solver later feeds to the unifier (Section 5.1).

**Function expressions (closures)**

For an anonymous function `fn(p1, …, pn) { body }` without parameter type annotations:

```text
Γ, p1 : ?a1, …, pn : ?an ⊢ body ⇝ (Tbody, Cbody)
-----------------------------------------------------------
Γ ⊢ fn(p1, …, pn) { body } ⇝ ((?a1, …, ?an) -> Tbody, Cbody)
```

where `?a1.. ?an` are fresh metas for the parameter types. If parameter annotations are present, they act like binding annotations: the parameter types are fixed to the annotated types and the body is checked under those; any mismatch between the inferred parameter types and the annotations is reported as an equality failure.

Closures are values for the purposes of the value restriction (Section 3.4): a binding `x = fn(...) { ... }` is eligible for generalization if it meets the other conditions.

### A.2 Method Calls and Receivers

Method calls `recv.m(e1, …, en)` are typed similarly to function calls, but additionally generate a `Recv` predicate tying the receiver expression's type to the method's logical receiver type.

Assume we have already resolved `m` to a particular trait method with scheme:

```text
forall[a1..ak]. P => (RecvTy, A1, …, An) -> R
```

Then:

```text
Γ ⊢ recv ⇝ (Trecv_expr, Crecv)
Γ ⊢ e1 ⇝ (T1, C1)   …   Γ ⊢ en ⇝ (Tn, Cn)
(P', (RecvTy', A1', …, An') -> R') = instantiate(forall[a1..ak]. P => (RecvTy, A1, …, An) -> R)
---------------------------------------------------------------
Γ ⊢ recv.m(e1, …, en) ⇝ (R', Crecv ∪ C1 ∪ … ∪ Cn
                                   ∪ P'
                                   ∪ { Recv[RecvTy', Trecv_expr],
                                        T1 == A1', …, Tn == An' })
```

Intuitively:

- We type the receiver and arguments as usual.
- We instantiate the method's scheme, producing:
  - A monomorphic function type `(RecvTy', A1', …, An') -> R'`.
  - A set of predicate constraints `P'`.
- We emit:
  - A `Recv[RecvTy', Trecv_expr]` predicate to capture auto-ref/deref from the expression type to the method's receiver type.
  - Equalities tying each argument type `Ti` to its corresponding parameter type `Ai'`.
  - The predicates `P'` as wanteds.

The goal solver later:

- Uses `Recv` to choose a legal auto-ref/deref chain and unify `RecvTy'` with the adjusted receiver type.
- Uses `P'` and the class environment to resolve the trait instance backing this method call.

**Operators**

All unary and binary operators are typed via their corresponding traits.

For a binary operator `op` with associated trait `OpTrait[Left, Right, Result]`:

```text
Γ ⊢ e1 ⇝ (T1, C1)
Γ ⊢ e2 ⇝ (T2, C2)
fresh ?r
-------------------------------------------------
Γ ⊢ e1 op e2 ⇝ (?r, C1 ∪ C2 ∪ { OpTrait[T1, T2, ?r] })
```

Specific operators (e.g. `+`, `-`, `<`, `==`) map to specific traits (`Add`, `Sub`, `Lt`, `Eq`, etc.) with appropriate parameter roles; the typing rule is the same shape, adding a class predicate for the operator and leaving the result type as a meta to be determined by instance resolution and surrounding constraints.

For a unary operator `uop` with associated trait `UnaryOpTrait[Arg, Result]` (e.g. numeric negation, logical not):

```text
Γ ⊢ e ⇝ (T, C)
fresh ?r
-------------------------------------------------
Γ ⊢ uop e ⇝ (?r, C ∪ { UnaryOpTrait[T, ?r] })
```

Again, specific unary operators map to specific traits (`Neg`, `Not`, etc.), but the typing rule simply adds the corresponding class predicate over the argument and result types.

### A.3 Records and Fields

**Struct construction**

For a nominal struct constructor `A { f1: e1, …, fn: en }` with declared field types `DeclTy(A, fi)`:

```text
Γ ⊢ e1 ⇝ (T1, C1)   …   Γ ⊢ en ⇝ (Tn, Cn)
------------------------------------------------
Γ ⊢ A { f1: e1, …, fn: en } ⇝ (A, C1 ∪ … ∪ Cn ∪ { T1 == DeclTy(A, f1), …, Tn == DeclTy(A, fn) })
```

Field shorthand `A { x, y: e }` is desugared in the frontend to the explicit form `A { x: x, y: e }` before typing.

**Field access**

For field access `e.x`:

```text
Γ ⊢ e ⇝ (Te, Ce)
------------------------------------------------
Γ ⊢ e.x ⇝ (Tx, Ce ∪ { HasField[Te, "x", Tx] })
```

where:

- `Tx` is a fresh type variable (meta) for the field type.
- `HasField[Te, "x", Tx]` is a predicate that the goal solver resolves by consulting the nominal definition of `Te` and unifying `Tx` with the declared type of field `x`.

### A.4 Blocks

Ray treats statements as expressions, so blocks use the same judgment `Γ ⊢ e ⇝ (T, C)`.

For a block `{ e1; e2; …; en }` where `n >= 1`:

```text
Γ ⊢ e1 ⇝ (T1, C1)   …   Γ ⊢ en ⇝ (Tn, Cn)
-------------------------------------------------
Γ ⊢ { e1; …; en } ⇝ (Tn, C1 ∪ … ∪ Cn)
```

If the block has no trailing expression (all items are bindings or discarded expressions), the frontend desugars it so that the last expression is an explicit `()` value of type `unit`.

### A.5 Trait and Impl Method Bodies

Trait and impl methods are always explicitly annotated and are checked, not inferred. Given a trait or impl method with declared scheme:

```text
forall[a1..an]. P => T
```

the checker skolemizes and checks the body expression `e` as follows:

1. Introduce skolems `s1..sn` for each `ai`.
2. Add `P[ai := si]` to the givens at the method's root constraint-tree node.
3. Extend `Γ` with the method's parameters typed according to `T[ai := si]`.
4. Type-check the body expression:

```text
Γ ⊢ e ⇝ (Te, Ce)
```

5. Emit an equality constraint `Te == T[ai := si]` and attach the constraints `Ce` to the method's root node.

In summary, method bodies are checked against their declared polymorphic types using skolemization; no additional polymorphism is inferred for them, and any mismatch between the body's inferred type `Te` and the instantiated signature `T[ai := si]` results in an equality failure at the method site.

### A.6 Control Flow and Return

**If expressions**

For a conditional expression `if cond { e_then } else { e_else }`:

```text
Γ ⊢ cond ⇝ (Tcond, Ccond)
Γ ⊢ e_then ⇝ (T_then, C_then)
Γ ⊢ e_else ⇝ (T_else, C_else)
-------------------------------------------------------------
Γ ⊢ if cond { e_then } else { e_else } ⇝ (T, Ccond ∪ C_then ∪ C_else ∪ { Tcond == bool, T_then == T_else, T == T_then })
```

where:

- `T` is the overall type of the `if` expression.
- If one branch has type `never`, unification treats `never` as bottom and does not constrain `T`; the other branch determines the result type.

**Pattern-if**

In guard positions, Ray supports a small pattern language:

- Wildcard `_`, which never binds any names.
- Plain bindings `x`, which introduce `x : Te` when guarding an expression of type `Te`.
- The nilable pattern `some(x)`, described below, which constrains the scrutinee to `nilable[T]` and introduces `x : T` for some `T`.

Ray supports an `if` form that combines such a pattern with a condition, such as:

```text
if some(x) = e { e_then } else { e_else }
```

For the concrete `some(x)` case, the typing rule is:

```text
Γ ⊢ e ⇝ (Te, Ce)
Te == nilable[T]    Γ ⊢ some(x) : nilable[T] ⇝ (Δ, Cp)
Γ, Δ ⊢ e_then ⇝ (T_then, C_then)
Γ ⊢ e_else ⇝ (T_else, C_else)
----------------------------------------------------------------
Γ ⊢ if some(x) = e { e_then } else { e_else } ⇝ (T,
                                                 Ce ∪ Cp ∪ C_then ∪ C_else
                                                 ∪ { T_then == T_else, T == T_then })
```

where:

- `Te` is constrained to be a `nilable[T]` for some `T`.
- `Δ` extends the environment in the `then` branch with `x : T`.
- `T` is the overall type of the `if` expression, unified with the branch types as above.

**Return expressions**

Return expressions `return e` are typed relative to the enclosing function's result type `Tret`:

```text
Γ ⊢ e ⇝ (Te, C)
-------------------------------------------------
Γ ⊢ return e ⇝ (never, C ∪ { Te == Tret })
```

where:

- `Tret` is the result type of the current function (either from its annotation or from a fresh meta assigned when the function type was introduced).
- The expression `return e` itself has type `never`, reflecting that control flow does not continue past this point.
- The equality `Te == Tret` ensures that the returned expression's type matches the function's declared (or inferred) return type; any mismatch is reported as an equality failure.

Because `never` is treated as a bottom type by unification, branches or expressions that contain `return` do not constrain surrounding expression types beyond the requirement that the returned expression matches `Tret`.

**While expressions**

For a loop `while cond { body }`:

```text
Γ ⊢ cond ⇝ (Tcond, Ccond)
Γ ⊢ body ⇝ (Tbody, Cbody)
-------------------------------------------------
Γ ⊢ while cond { body } ⇝ (unit, Ccond ∪ Cbody ∪ { Tcond == bool })
```

where:

- `body` is typed for its effects; its result type `Tbody` is not constrained by the `while`.

**Pattern-while**

Pattern-while combines the same pattern language with a loop guard, for example:

```text
while some(x) = e { body }
```

This is typed as:

```text
Γ ⊢ e ⇝ (Te, Ce)
Te == nilable[T]    Γ ⊢ some(x) : nilable[T] ⇝ (Δ, Cp)
Γ, Δ ⊢ body ⇝ (Tbody, Cbody)
--------------------------------------------------------------
Γ ⊢ while some(x) = e { body } ⇝ (unit, Ce ∪ Cp ∪ Cbody)
```

where `Te` is constrained to be `nilable[T]`, and `Δ` introduces `x : T` in the environment for the loop body.

**Loop and break**

Ray's `loop { body }` construct behaves like Rust's: it is an expression whose type is determined by the types of `break e` expressions inside it.

- The checker associates each `loop` with a fresh meta `?L` representing the loop's result type.
- Inside the loop, `break e` is typed analogously to `return e`, but targeting `?L`:

```text
Γ ⊢ e ⇝ (Te, C)
-------------------------------------------------
Γ ⊢ break e ⇝ (never, C ∪ { Te == ?L })
```

- If no `break e` is reachable (or all breaks are `break` without a value), the loop's type collapses to `never`, reflecting that control never falls through.

The exact control-flow analysis for reachability is an implementation detail, but the invariant is:

- Every `break e` inside a `loop` contributes an equality between its expression type and the loop's result type meta `?L`.
- The loop expression itself has type `?L` if any such break is reachable; otherwise it has type `never`.

For `break` without a value, the language treats it as sugar for `break ()`, so it is typed as:

```text
Γ ⊢ break ⇝ (never, ∅)   // plus the implicit equality () == ?L via the desugaring
```

The `continue` expression:

```text
Γ ⊢ continue ⇝ (never, ∅)
```

does not constrain any types; it only affects control flow.

**For loops**

Ray's `for` loops have the form:

```text
for pat in e { body }
```

and rely on a trait `Iter[Recv, Elem]` that relates an iterable type to its element type.

Typing rule:

```text
Γ ⊢ e ⇝ (Te, Ce)
Γ ⊢ pat : Tel ⇝ (Δ, Cpat)
Γ, Δ ⊢ body ⇝ (Tbody, Cbody)
-------------------------------------------------------------
Γ ⊢ for pat in e { body } ⇝ (unit,
                              Ce ∪ Cpat ∪ Cbody ∪ { Iter[Te, Tel] })
```

where:

- `Tel` is the element type of the iterator, introduced as a fresh meta if needed.
- `Iter[Te, Tel]` is a class predicate that the goal solver resolves using instances of the `Iter` trait.
- The overall type of the `for` expression is `unit`; it is used for its effects.

**Let-else pattern statement**

Ray may also support a let-else style pattern construct, analogous to Rust's `let Some(p) = expr else { body }`, written in Ray as:

```text
some(p) = e else { body }
```

This form:

- Evaluates `e` once.
- Attempts to match the `some(p)` pattern against the result.
- On success:
  - Binds the variables in `p` as in the `some(p)` pattern rule (Section A.7).
  - Control flow continues after the statement, with those bindings in scope.
- On failure:
  - Executes the `body` and does not return to the following code (e.g. because `body` returns, breaks, or otherwise diverges).

Typing rule:

```text
Γ ⊢ e ⇝ (Te, Ce)
Te == nilable[T]    Γ ⊢ some(p) : nilable[T] ⇝ (Δ, Cp)
Γ ⊢ body ⇝ (Telse, Celse)
---------------------------------------------------------------
Γ ⊢ some(p) = e else { body } ⇝ (unit,
                                  Ce ∪ Cp ∪ Celse ∪ { Telse == never })
```

where:

- `Te` is constrained to be `nilable[T]` for some `T`.
- `Δ` extends the environment with the bindings introduced by `p` at any program point following the statement (the success path).
- The `body` is required to have type `never` (or to be unifiable with `never`), reflecting that control flow does not continue past the `else` branch on failure.

### A.7 Patterns

Patterns are typed with a separate judgment:

```text
Γ ⊢ p : T ⇝ (Δ, C)
```

meaning: under environment `Γ`, pattern `p` is expected to match a scrutinee of type `T`, introduces new bindings `Δ` (a mapping from names to types), and generates additional constraints `C` (typically equalities).

**Variable pattern**

For a simple binding pattern `x`:

```text
Γ ⊢ x : T ⇝ ({ x : T }, ∅)
```

This introduces `x` with type `T` and no extra constraints.

**`some(p)` pattern on `nilable`**

The `some(p)` pattern matches the `some` constructor of a `nilable[T]` scrutinee and forwards typing to an inner pattern `p` on the payload type `T`:

```text
Γ ⊢ p : T ⇝ (Δ, C)
---------------------------------
Γ ⊢ some(p) : nilable[T] ⇝ (Δ, C)
```

This generalizes the common `some(x)` case, where `p` is just a variable pattern and `Δ = { x : T }`. The pattern introduces the same bindings as `p` and adds no constraints beyond the requirement that the scrutinee has type `nilable[T]`.

**Tuple and sequence patterns**

Tuple and sequence patterns destructure tuple-typed scrutinees. We write the tuple type of arity `n` as `tuple[T1, …, Tn]`. For a tuple pattern `(p1, …, pn)`:

```text
Γ ⊢ p1 : T1 ⇝ (Δ1, C1)   …   Γ ⊢ pn : Tn ⇝ (Δn, Cn)
-----------------------------------------------------------------
Γ ⊢ (p1, …, pn) : tuple[T1, …, Tn] ⇝ (Δ1 ∪ … ∪ Δn, C1 ∪ … ∪ Cn)
```

Sequence patterns `p1, …, pn` (without surrounding parentheses) are treated as syntactic sugar for the corresponding tuple pattern `(p1, …, pn)`. In all cases, we assume that patterns do not bind the same name with incompatible types inside a single pattern; the frontend is responsible for rejecting obviously conflicting bindings.

Because unit is represented as the empty tuple, a vacuous tuple pattern `()` matches only the unit type and introduces no bindings:

```text
Γ ⊢ () : tuple[] ⇝ (∅, ∅)
```

**Nested patterns**

Patterns compose structurally. For example:

- `some((x, y))` is interpreted as `some(p)` where `p` is the tuple pattern `(x, y)`, so it matches a scrutinee of type `nilable[tuple[T1, T2]]` and introduces `x : T1, y : T2`.
- More deeply nested patterns, such as `(a, some(b))` or `some(some(x))`, are typed by repeatedly applying the rules above: each layer constrains the expected type of its scrutinee and extends the environment with the bindings introduced by its subpatterns.

There are two primary pattern *roles* in the language:

- **Assignment patterns** are the patterns that appear as `lhs` in assignment expressions `lhs = rhs` (Section A.8). For assignment patterns:
  - The general binding/destructuring rule still uses `Γ ⊢ lhs : T ⇝ (Δ, C)`.
  - However, the surface syntax restricts `lhs` to variable, tuple/sequence, and (eventually) struct patterns; the `some(p)` form is not allowed on the left-hand side of an assignment.
  - Mutation-specific rules in A.8 further restrict which patterns may refer to existing locations (`x`, `*p`, `e.x`, `container[index]`).

- **Guard patterns** are patterns that appear in guard contexts such as `if some(p) = e`, `while some(p) = e`, and `for pat in e`. Guard patterns may use the full pattern language described here, including `some(p)` and nested combinations.

### A.8 Bindings, assignment, and mutation

Ray has a single assignment expression form `lhs = rhs`. Depending on what `lhs` denotes in the current scope, a given assignment can:

- **Introduce one or more bindings** (when `lhs` is a pattern that introduces fresh names, such as `x`, `(a, b)`, or a sequence), or
- **Mutate one or more existing locations** (when `lhs` refers to already-bound variables, dereferences, fields, or indices).

In all cases, assignment expressions have type `unit`; their primary effect is to generate constraints that tie the right-hand side type to the location type(s) and to update the binding-group environment when new names are introduced via destructuring.

In the current Ray surface language, the left-hand side of an assignment is always a pattern (Section A.7). We distinguish:

- **Binding/destructuring patterns**, which may introduce new names and can be arbitrarily nested:
  - Simple names: `x = e`, `mut x = e`
  - Tuple and sequence patterns: `(a, b) = e`, `a, b = e`, `(a, (b, c)) = e`
  - (Future) struct patterns such as `A { x, y } = e`
- **Mutation targets**, which must refer to existing locations and are limited to primitive l-value shapes:
  - Simple variable: `x = e` where `x` is already bound in the scope
  - Dereference: `*p = e`
  - Field projection: `e.x = rhs`
  - Index expression: `container[index] = rhs`

Complex patterns on the left-hand side are therefore legal for binding/destructuring assignment and are typed via the general pattern judgment from Section A.7. The `some(p)` pattern is reserved for guard contexts (`if some(p) = e`, `while some(p) = e`, `for some(p) in e`) and is not used as an assignment target. Mutation is currently specified only for the primitive l-value shapes above; more elaborate destructuring-mutation combinations are considered frontend sugar over sequences of simple assignments and do not require additional typing rules.

There is a single surface form `x = e` that covers both:

- **Binding assignment** (first introduction of `x` in a scope), and
- **Re-assignment** (updating an existing `x`).

Name resolution determines which case applies; the typing rules below describe both.

**Binding assignment `x = e` / `mut x = e`**

When `lhs` is a binding pattern that introduces only fresh names in the current scope, the assignment acts as a binding/destructuring assignment. The general rule uses the pattern typing judgment from Section A.7:

```text
Γ ⊢ rhs ⇝ (Trhs, Crhs)
Γ ⊢ lhs : Trhs ⇝ (Δ, Cp)
-----------------------------------
Γ ⊢ lhs = rhs ⇝ (unit, Crhs ∪ Cp)
```

where `Δ` maps each newly bound name in `lhs` to its type. This covers simple bindings `x = e`, `mut x = e`, as well as tuple and sequence destructuring such as `(a, b) = e`.

For the common single-name case:

```text
Γ ⊢ e ⇝ (T, C)
Γ ⊢ x = e ⇝ (unit, C)
```

and similarly for `mut x = e`. The binding-group machinery:

- Records that `x` is bound in this scope with inferred type `T`.
- Decides at the binding-group root whether `x` is generalized into a scheme or remains monomorphic (Section 3.4).

We write assignments as `lhs = rhs`, where `lhs` is a pattern.

**Simple variable assignment**

For re-assignment to an existing variable `x` (i.e. when `Γ(x) = T` is already present from a previous binding in this scope):

```text
Γ(x) = T
Γ ⊢ e ⇝ (Te, Ce)
-------------------------------------------------
Γ ⊢ x = e ⇝ (unit, Ce ∪ { Te == T })
```

This rule describes the re-assignment case. For first-time bindings `x = e` and `mut x = e`, Section A.4 applies: the binding-group machinery records `x : T` and later decides whether `x` is generalized or stays monomorphic.

**Deref assignment `*p = e`**

Ray represents dereference patterns using the core `Deref[Ptr, Elem]` trait (see `lib/core/deref.ray`). For an assignment to a dereferenced pointer:

```text
Γ ⊢ p ⇝ (Tp, Cp)
Γ ⊢ e ⇝ (Te, Ce)
fresh Tcell
--------------------------------------------------------------
Γ ⊢ *p = e ⇝ (unit,
              Cp ∪ Ce ∪ { Deref[Tp, Tcell], Te == Tcell })
```

Intuitively:

- `Tp` is the type of the pointer expression `p`.
- `Deref[Tp, Tcell]` is a class predicate requiring that `Tp` can be dereferenced to an element type `Tcell`.
- The right-hand side expression `e` must have type `Tcell`.

Whether `Tp` is actually mutable and whether deref-assignment is permitted for a given pointer type is enforced by the mutability and ownership system, not by the type system rules here; from the type system's point of view, deref-assignment is well-typed if there is a suitable `Deref` instance and the right-hand side matches the dereferenced type.

**Field assignment `e.x = rhs`**

Field assignment updates a field of a nominal record:

```text
Γ ⊢ e ⇝ (Te, Ce)
Γ ⊢ rhs ⇝ (Trhs, Crhs)
fresh Tx
--------------------------------------------------------------
Γ ⊢ e.x = rhs ⇝ (unit,
                  Ce ∪ Crhs ∪ { HasField[Te, "x", Tx], Trhs == Tx })
```

Here:

- `HasField[Te, "x", Tx]` ensures that `Te` is a record type with a field `x` of type `Tx` (Section A.3).
- The right-hand side must have the same type `Tx`.

Again, whether `e.x` is actually a mutable location is handled by mutability checking; the typing rule only ensures type consistency between the field and the assigned expression.

**Index assignment `container[index] = rhs`**

Indexing uses the `Index[Container, Elem, Index]` trait (Section 2.2 and A.3). Assignment to an indexed element is typed by reusing this trait:

```text
Γ ⊢ container ⇝ (Tc, Cc)
Γ ⊢ index ⇝ (Ti, Ci)
Γ ⊢ rhs ⇝ (Trhs, Crhs)
fresh Tel
------------------------------------------------------------------
Γ ⊢ container[index] = rhs ⇝ (unit,
                               Cc ∪ Ci ∪ Crhs
                               ∪ { Index[Tc, Tel, Ti], Trhs == Tel })
```

This says:

- `container` has type `Tc`, `index` has type `Ti`.
- `Index[Tc, Tel, Ti]` must hold, relating the container and index types to an element type `Tel`.
- The right-hand side `rhs` must have type `Tel`.

As with field assignment, write-ability is enforced by the mutability/borrowing discipline; the type system only checks that the assigned value matches the element type implied by the `Index` predicate.

**Compound assignment `lhs op= rhs`**

Compound assignments (e.g. `x += 1`, `e.x *= 2`) are desugared in the frontend into plain assignments plus the corresponding binary operator:

```text
lhs op= rhs    ≡    lhs = lhs op rhs
```

with the additional syntactic restriction (enforced by the frontend) that `lhs` must be an l-value such as a simple name or a field path. After desugaring, the type checker sees only:

- The assignment typing rules above for `lhs = ...`.
- The operator typing rules from Section A.2 for `lhs op rhs`.

There is no separate type-system rule for `op=` itself.

### A.9 Cast expressions

Ray supports cast expressions of the form `e as Tcast`. Casts are distinct from annotations: they request a type conversion, not a check that `e` already has type `Tcast`.

Algorithmically, we treat casts as changing the expression's type to the target type without adding equality constraints between the source and target types:

```text
Γ ⊢ e ⇝ (Te, C)
-----------------------------------
Γ ⊢ e as Tcast ⇝ (Tcast', C)
```

where `Tcast'` is the monomorphic type denoted by `Tcast`. The detailed set of allowed casts (which conversions are permitted, whether they are safe or unsafe) is defined by the language and runtime and is not part of this type system specification. The type checker only ensures that both `Te` and `Tcast'` are well-formed types and that the cast expression itself is well-typed with result type `Tcast'`.

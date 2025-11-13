# Pointer Arithmetic

Ray’s pointer arithmetic story focuses on explicit, unsafe operations that allow `*'a` pointers to move by integer offsets without round-tripping through integers. This document captures the current requirements, unsafe semantics, trait-model changes, and the implementation roadmap.

## Scope & Requirements
- **Operators**: Only `+` and `-` are in scope. They accept a `*'a` pointer on the left and a `uint` offset on the right, producing another `*'a`.
- **Operand validation**: LHS must be a raw pointer type; RHS must be an integer compatible with `uint`. Pointer subtraction is only defined when both operands share the same pointee type; mismatches raise a type error.
- **Allocation provenance**: Arithmetic must stay within the allocation that produced the pointer. The compiler cannot currently prove this, so we document that violating it is undefined behavior.
- **Overflow/underflow**: Crossing the machine address space traps or is undefined behavior (decision pending). Diagnostics should note the risk.
- **Casting**: `cast` between pointers and integers remains available for advanced scenarios, but ordinary arithmetic should no longer require it.

## Unsafe Model
- Pointer arithmetic is always considered unsafe. Expressions like `ptr + n` or `ptr - n` must appear inside `unsafe ( ... )` (or future `unsafe { ... }` blocks).
- The parser already accepts `unsafe <expr>`; semantic analysis must flag pointer arithmetic with `RequiresUnsafe::PointerArithmetic` so the checker can ensure it resides in an unsafe context.
- When used outside `unsafe`, emit a diagnostic such as: “pointer arithmetic is unsafe; wrap the expression in `unsafe (...)`,” ideally pointing at the operator token and offering a fix-it.

## Operator Traits with Multiple Operands
- The existing operator traits (`Add`, `Sub`, etc.) only model a single type parameter (the implementor), which prevents heterogeneous operands. Ray’s impl declarations use `impl Trait[TypeArgs] { ... }`, so we simply spell the differing operand types inside those brackets when needed.
- Redefine each trait with associated types:
  ```ray
  trait Add {
      type Lhs = Self;
      type Rhs = Self;
      type Output = Self;
      fn add(lhs: Lhs, rhs: Rhs) -> Output;
  }
  ```
  `Sub`, `Mul`, and the rest follow the same pattern.
- Existing impls continue to work because the defaults mirror today’s behavior. New impls override `Rhs`/`Output` when needed.
- During operator resolution, the trait solver constrains `Lhs` to the left operand type, `Rhs` to the right operand type, and treats `Output` as the expression’s result. Errors should mention both operands when no impl fits.

## Pointer Arithmetic Implementations
- Add intrinsic-style impls in `lib/core/ops.ray`:
  ```ray
  impl Add[*'a, uint] {
      type Lhs = *'a;
      type Rhs = uint;
      type Output = *'a;

      fn add(lhs: *'a, rhs: uint) -> *'a {
          unsafe { __ptr_add(lhs, rhs) }
      }
  }
  ```
  `Sub` mirrors this.
- `__ptr_add`/`__ptr_sub` are compiler intrinsics or `todo!()` placeholders until codegen handles them. They preserve pointer provenance and keep any const/mut qualifiers intact.
- These impls (or their MIR/IR equivalents) must mark that they require unsafe evaluation so diagnostics remain accurate.

## Compiler & IR Work
- **AST/HIR**: Ensure trait declarations record associated types so semantic analysis can read `Lhs`, `Rhs`, and `Output`. No syntax change is needed for operator expressions.
- **Trait solver**: Update resolution to bind `Lhs`/`Rhs` constraints and infer `Output`. Extend diagnostics to show both operand types on failure.
- **Unsafe tracking**: When operator resolution selects the pointer impl, emit a `PointerArithmetic` unsafe requirement. The surrounding expression must be `Expr::Unsafe`.
- **Lowering**: Introduce IR nodes or intrinsics (`PtrAdd`, `PtrSub`) that accept a pointer and `uint`, returning a pointer. Codegen expands them into the target’s pointer arithmetic instructions while preserving provenance.

## Testing & Documentation
- Add semantic tests (or TODOs) covering:
  - Successful `unsafe (ptr + n)` and `unsafe (ptr - n)`.
  - Errors for missing `unsafe`.
  - Type mismatches (`*'a + float`, pointer subtraction between different pointee types).
- Update docs (standard library overview, language reference) to mention that pointer arithmetic is limited to `+/-` with `uint` and always requires `unsafe`.

## Future Extensions
- Once multi-operand traits ship, other heterogenous operators (e.g., vector/scalar) can reuse the same mechanism.
- Add slice helpers (`slice.as_ptr`, `ptr.offset`, etc.) that wrap the intrinsic operations behind unsafe APIs.
- Consider runtime bounds/debug assertions or sanitizer hooks to detect allocation-crossing pointer math during development builds.

This plan keeps pointer arithmetic explicit, unsafe, and minimal while paving the way for richer operator support elsewhere in the language.

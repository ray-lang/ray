# References & Pointer Model

Ray uses a unified reference model built on five reference types — three heap-allocated capability types (`*mut T`, `*T`, `id *T`) and two borrow types (`&T`, `&mut T`) — with automatic reference counting for heap references and fully inferred regions. The goal is memory safety without surface lifetime annotations, while keeping the mental model simple: **unique references can mutate, shared references cannot, identity references only compare, and borrows are temporary aliases with no refcount overhead.**

This document is a design specification. It describes the target semantics, not the current implementation.

---

## 1. Reference Capability Types

Every reference in Ray carries a *capability* that governs what operations are permitted through it.

### 1.1 `*mut T` — Unique, Mutable

- The only way to mutate a heap-allocated object.
- Non-copyable: at most one `*mut T` exists for a given allocation at any time.
- Produced by `new(T)` or `box(expr)`.
- The holder of `*mut T` is the **owner** of the object.
- **Not allowed as a struct field** (see [§1.7](#17-unique-references-are-not-allowed-in-struct-fields)).
- Local-only: exists as variables, parameters, and return values.

```ray
mut obj = box(Point { x: 1, y: 2 })
obj.x = 42                            // mutation through *mut Point
```

### 1.2 `*T` — Shared, Read-Only

- Permits reading fields and calling methods, but not mutation.
- Copyable: each copy increments the strong reference count.
- Produced by `freeze(x)` where `x: *mut T`.
- Once an object is shared, it is immutable through safe references (see [§13.1](#131-interior-mutability) for interior mutability).

```ray
mut obj = box(Point { x: 1, y: 2 })
obj.x = 42
shared = freeze(obj)                   // shared: *Point, obj is consumed
other = shared                         // copy, strong refcount now 2
```

### 1.3 `id *T` — Identity-Only

- Cannot read fields, call methods, or take the address of the referent.
- The only permitted operations are identity comparison (`==`, `!=`) and `upgrade`.
- Copyable: each copy increments the weak reference count.
- Produced by `id(x)` where `x: *T`.
- Acts as a **weak reference**: does not keep the object alive.

```ray
shared = freeze(box(Foo { value: 1 }))
identity = id(shared)                  // identity: id *Foo, shared is NOT consumed
```

### 1.4 `&T` — Shared Borrow

- A temporary, read-only reference to a value. Permits reading fields and calling methods, but not mutation.
- **Not reference-counted.** No heap header, no IncRef/DecRef. The referent may live on the stack or the heap.
- Copyable: copying a `&T` is a plain pointer copy with no refcount effect.
- Produced by `&x` where `x: T` (address-of a stack value), or by implicit coercion from `*T` or `*mut T`.
- The borrow is constrained to a **region** ([§7](#7-regions--lifetime-safety)) — it cannot outlive the referent.

```ray
p = Point { x: 1, y: 2 }
ref = &p                               // ref: &Point, borrows p on the stack

shared = freeze(box(Point { x: 3, y: 4 }))
borrow = shared                        // borrow: &Point via implicit coercion (when &Point is expected)
```

### 1.5 `&mut T` — Unique Borrow

- A temporary, mutable reference to a value. Permits reading and writing fields and calling methods.
- **Not reference-counted.** No heap header, no IncRef/DecRef.
- Non-copyable: at most one `&mut T` to a given value exists at any time.
- Produced by `&mut x` where `mut x: T` (address-of a mutable stack value), or by implicit coercion from `*mut T`.
- The borrow is constrained to a **region** — it cannot outlive the referent.
- While a `&mut T` borrow is active, the original value (or reference) is unavailable.

```ray
mut p = Point { x: 1, y: 2 }
mref = &mut p                          // mref: &mut Point, borrows p mutably
mref.x = 42                            // mutation through the borrow
// p is unavailable while mref is active
```

### 1.6 Capability Lattice

Capabilities only weaken, never strengthen:

```
Heap (owned, RC'd):       *mut T  →  *T  →  id *T
                          (unique)   (shared)  (identity)

Borrow (temporary, no RC): &mut T  →  &T
                           (unique)   (shared)

Cross-kind coercions:      *mut T  →  &mut T
                           *T      →  &T
```

A heap reference can always be borrowed (coerced to the corresponding borrow type), but a borrow can never be promoted to a heap reference. Borrowing a heap reference does not affect its reference count — the borrow is a temporary, region-scoped alias.

The explicit weakening operations are:

| Operation    | Input    | Output  | Consuming?                     |
|--------------|----------|---------|--------------------------------|
| `freeze(x)`  | `*mut T` | `*T`    | Yes — `x` is consumed (moved)  |
| `id(x)`      | `*T`     | `id *T` | No — `x` remains valid         |

The implicit coercions are:

| Coercion         | Input     | Output   | When                                      |
|------------------|-----------|----------|-------------------------------------------|
| Borrow unique    | `*mut T`  | `&mut T` | Passing `*mut T` to a function or binding |
| Borrow shared    | `*T`      | `&T`     | Passing `*T` to a function or binding     |
| Weaken borrow    | `&mut T`  | `&T`     | Passing `&mut T` where `&T` is expected   |

There is no operation or coercion to strengthen a capability. A borrow cannot be promoted to an owned heap reference.

### 1.7 Unique References Are Not Allowed in Struct Fields

Struct fields may only contain value types, `*T`, `&T`, `id *T`, or `nilable` variants thereof. Unique references (`*mut T` and `&mut T`) are **not permitted** as struct field types.

```ray
struct Container {
    item: *Foo        // OK — shared heap reference
    parent: id *Bar   // OK — weak reference
    label: string     // OK — value type
    view: &Baz        // OK — shared borrow (region-constrained)
    // data: *mut Baz // ERROR — unique references not allowed in struct fields
    // edit: &mut Baz // ERROR — unique references not allowed in struct fields
}
```

**Rationale:** Unique references (`*mut T`, `&mut T`) are transient handles — `*mut T` is a setup handle during the unique phase, and `&mut T` is a temporary exclusive borrow. Disallowing them in fields ensures:

- All structs are copyable (all field types are copyable).
- Clone is always auto-derivable ([§10](#10-cloning)).
- No non-copyable struct complexity.
- The lifecycle is clear: create → mutate → freeze → store.

**Borrow fields (`&T`) and struct lifetime:** A struct containing `&T` fields borrows the referent — the region system ([§7](#7-regions--lifetime-safety)) ensures the referent outlives the struct. Such structs can live on the stack but cannot be heap-allocated (storing a borrow in a heap object would violate the outlives constraint). This is the correct model for types like iterators that temporarily borrow data without taking ownership.

For types that need exclusive heap ownership internally (e.g., `Vec`, `HashMap`), use unsafe `rawptr[T]` in the implementation.

### 1.8 Copyability

Copyability is a structural property:

| Type                                       | Copyable?                                                                          |
|--------------------------------------------|-------------------------------------------------------------------------------------|
| Primitives (`int`, `string`, `bool`, etc.) | Yes                                                                                 |
| `*T`                                       | Yes (copy bumps strong refcount)                                                    |
| `id *T`                                    | Yes (copy bumps weak refcount)                                                      |
| `&T`                                       | Yes (plain pointer copy, no refcount effect)                                        |
| `*mut T`                                   | No (unique)                                                                         |
| `&mut T`                                   | No (unique)                                                                         |
| `nilable[*T]`, `nilable[id *T]`            | Yes                                                                                 |
| Structs                                    | Yes (all fields are copyable, since unique reference fields are disallowed)         |
| Enums                                      | Yes (all variant payloads are copyable)                                             |

---

## 2. Object Lifecycle

### 2.1 Allocation

Ray provides two heap allocation primitives, both returning `*mut T`:

**`new(T)`** — zero-initialized allocation. `T` is a **type**, not a value. Allocates a heap object of type `T` with all fields set to their zero values, and returns `*mut T`:

```ray
mut p = new(Point)                     // p: *mut Point, Point { x: 0, y: 0 }
p.x = 1
p.y = 2
```

**`box(expr)`** — value-initialized allocation. `expr` is a **value expression**. Evaluates `expr`, heap-allocates storage, moves the result into it, and returns `*mut T`:

```ray
mut p = box(Point { x: 1, y: 2 })     // p: *mut Point, directly initialized
```

Both allocations start with `strong_count = 1, weak_count = 0`. The allocation layout is described in [§3](#3-reference-counting).

Array/buffer allocation is a separate concern handled by the unsafe `alloc(T, count)` primitive.

### 2.2 Zero Values

Every type has a zero value. For built-in types:

| Type                         | Zero Value                                    |
|------------------------------|-----------------------------------------------|
| `int`, `uint`, `i8`, etc.    | `0`                                           |
| `float`, `f32`, `f64`        | `0.0`                                         |
| `bool`                       | `false`                                       |
| `string`                     | `""`                                          |
| `nilable[T]`                 | `nil`                                         |
| `*T`                         | Heap-allocated zero-valued `T` (see below)    |
| `id *T`                      | Heap-allocated zero-valued `T` (weak ref)     |

**Structs**: the zero value of a struct is the struct with all fields set to their zero values.

**Reference fields and recursive allocation**: the zero value of `*T` is a heap-allocated zero-valued `T`. This means `new(Foo)` where `Foo` has a `parent: *Bar` field will allocate both a `Foo` and a zero-valued `Bar` for the `parent` field. Deeply nested reference fields cause recursive allocation.

To avoid recursive allocation costs, use `nilable[*T]` instead (zero value is `nil`, no allocation).

**Born-shared objects**: zero-valued `*T` fields create objects that enter the shared phase directly, skipping the unique phase. This is sound — the object is fully initialized with zero values and immediately shared at `strong_count = 1`. No `*mut T` to it ever existed.

### 2.3 Unique Phase

While a `*mut T` exists, the object is in its **unique phase**:

- Only one reference exists (the `*mut T`).
- The owner may read and write fields freely.
- The owner may pass the reference to functions via temporary borrowing ([§6](#6-borrowing)).
- The owner may permanently transition to the shared phase via `freeze`.
- If the `*mut T` goes out of scope without being frozen, the object is destroyed ([§4](#4-destructors)).

### 2.4 Freezing

`freeze(x)` consumes a `*mut T` and produces a `*T`:

```ray
mut obj = box(Foo { value: 1 })
obj.value = 2                          // mutate during unique phase
shared = freeze(obj)                   // obj is consumed; shared: *Foo
// obj is no longer accessible here
```

Internally, this is a type-level operation — the pointer value is unchanged, the strong count remains 1. Only the capability changes.

### 2.5 Shared Phase

Once frozen, the object enters its **shared phase**:

- Any number of `*T` copies may exist; each copy increments the strong count.
- `id *T` references may be derived; each increments the weak count.
- The object is immutable through safe references.
- When the last `*T` is dropped (strong count → 0), the object is destroyed ([§4](#4-destructors)).

### 2.6 Upgrade

`upgrade(x)` attempts to convert an `id *T` back to a `*T`:

```ray
if some(result) = upgrade(identity) {
    // result: *Foo — object is still alive
} else {
    // object has been destroyed
}
```

- Returns `nilable[*T]`.
- If `strong_count > 0`: increments the strong count and returns the `*T`.
- If `strong_count == 0`: the object is already destroyed; returns `nil`.

---

## 3. Reference Counting

### 3.1 Allocation Layout

Every heap-allocated object has the following layout:

```
┌──────────────┬──────────────┬──────────────┐
│ strong_count │  weak_count  │     data     │
│    (uint)    │    (uint)    │     (T)      │
└──────────────┴──────────────┴──────────────┘
```

- `strong_count`: number of live `*T` and `*mut T` references.
- `weak_count`: number of live `id *T` references.
- `data`: the actual object data of type `T`.

### 3.2 Count Operations

| Event                    | strong_count  | weak_count |
|--------------------------|---------------|------------|
| `new(T)` or `box(expr)`  | 1             | 0          |
| Copy a `*T`              | +1            | —          |
| Drop a `*T` or `*mut T`  | −1            | —          |
| `id(x)`                  | —             | +1         |
| Copy an `id *T`          | —             | +1         |
| Drop an `id *T`          | —             | −1         |
| `freeze(x)`              | — (unchanged) | —          |
| `upgrade(x)` (success)   | +1            | —          |

### 3.3 Deallocation Sequence

When `strong_count` reaches 0:

1. Run the user-defined `Destruct` implementation, if any ([§4](#4-destructors)).
2. Recursively drop all fields (decrement refcounts of reference-typed fields, destruct nested values).
3. Deallocate the `data` portion of the allocation.
4. If `weak_count == 0`: deallocate the entire allocation (including the control header).
5. If `weak_count > 0`: keep the control header (strong_count + weak_count) alive. The data portion is freed but the header persists until the last `id *T` is dropped.

When `weak_count` reaches 0 **and** `strong_count` is already 0:

6. Deallocate the control header.

This ensures that `id *T` references never dangle at the pointer level — the allocation address is stable until all weak references are gone, making identity comparison sound (no ABA problem).

---

## 4. Destructors

### 4.1 The `Destruct` Trait

```ray
trait Destruct['a] {
    fn destruct(*mut 'a)
}
```

- Called when the strong reference count reaches 0.
- Receives `*mut self`, even if the last reference was a `*T`. This is sound because `strong_count == 0` guarantees exclusive access — no other reference can observe the object.
- Runs **before** compiler-generated field drops.
- User code in `destruct` may mutate the object (e.g., flushing buffers, closing handles).

### 4.2 Compiler-Generated Drops

After the user-defined `destruct` (if any) returns, the compiler generates code to:

1. For each field of reference type (`*T`, `id *T`): decrement the appropriate refcount, potentially triggering cascading destructions.
2. For each field of value type containing references: recursively apply the same process.
3. Deallocate the object's data.

### 4.3 Drop Order

Fields are dropped in **declaration order** (first field declared is dropped first). This matches the order a programmer would expect when reading the struct definition.

### 4.4 Destructor Restrictions

- A `destruct` implementation must not store `self` or any reference derived from `self` into a location that outlives the destructor call. The region system ([§7](#7-regions--lifetime-safety)) enforces this — the `*mut self` has a destructor-scoped region that cannot escape.
- A `destruct` implementation must not panic. (Panic-in-destructor semantics are undefined for now; future work may define double-fault behavior.)

---

## 5. Address-of Operators

The `&` and `&mut` operators create borrows from stack values:

| Expression | Input                    | Result                   | Notes                               |
|------------|--------------------------|--------------------------|-------------------------------------|
| `&x`       | `x: T` (stack value)     | `&T` in x's region       | Shared borrow of immutable value    |
| `&mut x`   | `mut x: T` (stack value) | `&mut T` in x's region   | Unique borrow of mutable value      |

```ray
p = Point { x: 1, y: 2 }
ref = &p                               // ref: &Point, in p's stack region

mut q = Point { x: 3, y: 4 }
mref = &mut q                          // mref: &mut Point, in q's stack region
```

These references live in the **stack region** of the lvalue. Region constraints ([§7](#7-regions--lifetime-safety)) prevent them from escaping to longer-lived storage.

`&` and `&mut` are only for creating references from stack values. For passing references to functions, see [§6](#6-borrowing).

---

## 6. Borrowing

Borrowing provides temporary, scoped access to a value without taking ownership. With borrow types (`&T`, `&mut T`), borrowing is expressed directly in function signatures — a function declares whether it needs ownership (`*T`, `*mut T`) or just temporary access (`&T`, `&mut T`).

### 6.1 Implicit Coercion at Call Sites

When a heap reference is passed to a function expecting a borrow, the compiler implicitly coerces it:

```ray
fn reset(p: &mut Point) {
    p.x = 0
    p.y = 0
}

mut obj = box(Point { x: 1, y: 2 })
reset(obj)                          // *mut Point coerced to &mut Point
obj.x = 3                           // obj is available again after the call
```

```ray
fn print_point(p: &Point) {
    // read-only access to p
}

mut obj = box(Point { x: 1, y: 2 })
print_point(obj)                    // *mut Point coerced to &Point
obj.x = 3                           // obj: *mut Point is available again

shared = freeze(box(Point { x: 5, y: 6 }))
print_point(shared)                 // *Point coerced to &Point
```

Internally:
- A fresh region `ρ'` is created, constrained to be no longer than the call duration.
- The callee receives a borrow (`&ρ' T` or `&mut ρ' T`).
- If the source is `*mut T`, the original is marked **unavailable** for the duration of the call.
- After the call returns, the original becomes available again.

The coercion rules follow the capability lattice ([§1.6](#16-capability-lattice)): `*mut T` → `&mut T` → `&T`, and `*T` → `&T`. No reference count is affected — the borrow is a temporary alias.

### 6.2 Path-Level Borrowing

Multiple disjoint fields of a `*mut T` (or `&mut T`) may be borrowed simultaneously:

```ray
fn swap_coords(x: &mut int, y: &mut int) {
    mut tmp = *x
    *x = *y
    *y = tmp
}

mut p = box(Point { x: 1, y: 2 })
swap_coords(p.x, p.y)             // borrows p.x and p.y independently
```

Rules:
- Two borrows are **disjoint** if they access different fields at every level of nesting.
- Borrowing `p.x` and `p.y` simultaneously is allowed (disjoint fields).
- Borrowing `p.x` and `p` simultaneously is **not** allowed (the second covers the first).
- For constant-length array types, individual elements at statically-known indices are treated as disjoint paths (e.g., `arr[0]` and `arr[1]`).
- Dynamic array indexing is **not** eligible for path-level borrowing (the compiler cannot prove disjointness).

### 6.3 Implicit Auto-ref for Method Receivers

When a method expects a reference receiver and is called on a value lvalue, the compiler inserts an implicit address-of operation:

```ray
impl object Point {
    fn scale(&mut self, factor: int) {
        self.x = self.x * factor
        self.y = self.y * factor
    }
}

mut p = Point { x: 1, y: 2 } // p is a stack-allocated value
p.scale(3)                   // compiler inserts &mut p, creating &mut Point
```

This allows the same method definition to work on both stack values and heap references without the programmer writing different code for each case.

Auto-ref applies **only to method receivers**, not to regular function arguments. For regular function arguments, use `&` / `&mut` explicitly when passing stack values.

### 6.4 Closure Captures

Closures capture variables from their enclosing scope. The capture behavior depends on the captured variable's type:

| Captured type | Behavior                       | Rationale                    |
|---------------|--------------------------------|------------------------------|
| Value types   | **Copy**                       | No ownership semantics       |
| `&T`          | **Copy** (plain pointer copy)  | Borrows alias freely         |
| `*T`          | **Copy** (strong RC bump)      | Shared refs alias freely     |
| `id *T`       | **Copy** (weak RC bump)        | Identity refs alias freely   |
| `&mut T`      | **Move** (original consumed)   | Cannot alias unique borrows  |
| `*mut T`      | **Move** (original consumed)   | Cannot alias unique refs     |

#### Unique references are moved

A closure that captures a `*mut T` variable **moves** it — the original binding is consumed at the closure creation point:

```ray
fn example() {
    mut p = box(Point { x: 1, y: 2 })
    f = () => freeze(p) // p is moved into the closure here
    p                   // ERROR: use of consumed value `p`
}
```

This follows directly from the `*mut T` aliasing invariant ([§1.1](#11-mut-t--unique-mutable)): a closure capturing `p` creates a second path to the same object, which would violate uniqueness. Moving ensures only one path exists at any time.

Multiple closures cannot capture the same `*mut T`:

```ray
fn example() {
    mut p = box(42)
    f = () => freeze(p) // p is moved here
    g = () => freeze(p) // ERROR: use of consumed value `p`
}
```

#### Shared and identity references are copied

Closures freely capture `*T` and `id *T` references. Each capture increments the appropriate reference count:

```ray
fn example(shared: *Foo, weak: id *Bar) {
    f = () => {
        shared.value // shared is copied into closure (strong RC bump)
        weak         // weak is copied into closure (weak RC bump)
    }
    // shared and weak are still accessible here
}
```

#### Immediately-invoked closures

There is no special-casing for immediately-invoked closures. A closure that captures `*mut T` moves it at the capture point, regardless of when or whether the closure is called:

```ray
fn example() {
    mut p = box(42)
    (() => freeze(p))() // p is moved at closure creation
    // p is not accessible here
}
```

#### Future: `noescape` closures

A future extension may allow closures to **borrow** `*mut T` instead of moving it, when the closure is provably short-lived. This would use a `noescape` annotation on the function parameter receiving the closure:

```ray
fn with_lock(resource: &mut int, body: noescape fn() -> ()) {
    body()
    // body cannot be stored or returned — only called within this scope
}

fn example(p: &mut int) {
    with_lock(p, () => use(p))  // p is reborrowed, not moved
    p                           // still valid — borrow ended when with_lock returned
}
```

`noescape` is a property of the **parameter**, not the function type. The same function type `fn() -> ()` can appear in both escaping and non-escaping positions. The annotation is a promise by the callee that it will not store the closure beyond the call's duration.

When a closure is passed to a `noescape` parameter, captured `&mut T` and `*mut T` values are reborrowed for the call's duration — identical to how function arguments are coerced ([§6.1](#61-implicit-coercion-at-call-sites)). This ties into the region system ([§7](#7-regions--lifetime-safety)).

Without `noescape`, the default is escaping — `&mut T` and `*mut T` captures are always moves.

---

## 7. Regions & Lifetime Safety

### 7.1 Overview

Every reference is internally parameterized by a **region** representing its validity extent:

- Surface syntax: `*T`, `*mut T`, `id *T`, `&T`, `&mut T` (no region annotation).
- Internal representation: `*ρ T`, `*mut ρ T`, `id *ρ T`, `&ρ T`, `&mut ρ T`.

Regions are **never** written in source code. They are inferred by the compiler and used only for internal safety checking.

### 7.2 Region Kinds

| Kind              | Produced By                                                                   | Lifetime                                  |
|-------------------|-------------------------------------------------------------------------------|-------------------------------------------|
| Heap region       | `new(T)`, `box(expr)`, `upgrade(x)`                                           | Lives as long as the refcount is nonzero  |
| Stack region      | `&x`, `&mut x` on a stack lvalue                                              | Scoped to the enclosing stack frame       |
| Call region       | Implicit coercion ([§6.1](#61-implicit-coercion-at-call-sites)) | Scoped to the function call               |
| Destructor region | `*mut self` in `Destruct`                                                      | Scoped to the destructor body             |

### 7.3 Outlives Constraints

Assigning, storing, or returning a reference generates an **Outlives** constraint:

```
Outlives(ρ_src, ρ_dest)
```

Meaning: the source region `ρ_src` must live at least as long as the destination region `ρ_dest`.

Examples:

```ray
// Storing a reference in a struct field:
//   Outlives(ρ_ref, ρ_struct) — the reference must outlive the struct
mut s = box(Wrapper { inner: some_ref })

// Returning a reference from a function:
//   Outlives(ρ_ref, ρ_return) — the reference must outlive the caller's use site

// Storing in a global:
//   Outlives(ρ_ref, ρ_static) — only heap-rooted regions satisfy this
```

### 7.4 Safety Guarantees

The region system ensures:

1. **Borrows cannot escape their region**: a `&T` or `&mut T` derived from `&x` / `&mut x` on a stack variable has a stack-scoped region. Storing it in a heap-allocated struct would require `Outlives(ρ_stack, ρ_heap)`, which fails.

2. **Call-scoped borrows cannot escape**: a borrow produced by implicit coercion at a call site has a call-scoped region. Storing it in a struct or returning it would violate the outlives constraint.

3. **Heap references are freely storable**: references produced by `new` or `box` have heap-rooted regions that satisfy any outlives constraint.

4. **Destructor references cannot escape**: the `*mut self` in a destructor has a destructor-scoped region that cannot be stored or returned.

### 7.5 Error Messages

Since regions never appear in surface syntax, error messages must be phrased in terms of **user-visible constructs**:

| Internal Violation                  | User-Facing Message                                                                                             |
|-------------------------------------|------------------------------------------------------------------------------------------------------------------|
| `Outlives(ρ_stack, ρ_heap)` fails   | "cannot store a reference to local variable `x` in a heap-allocated struct — `x` does not live long enough"     |
| `Outlives(ρ_call, ρ_return)` fails  | "cannot return a reference to parameter `p` — the reference is only valid for the duration of the call"         |
| `Outlives(ρ_call, ρ_field)` fails   | "cannot store borrowed reference in field `foo.bar` — the borrow expires when this call returns"                |

The compiler must track the **provenance** of each region (which variable, allocation, or call it originates from) to produce these messages.

---

## 8. Method Calls & Auto-deref

### 8.1 Auto-deref

References are automatically dereferenced when accessing fields or calling methods:

```ray
shared = freeze(box(Point { x: 1, y: 2 }))
x = shared.x                               // auto-deref: reads field x through *Point
```

Auto-deref applies transitively: if `p: **T` (a reference to a reference), `p.field` dereferences twice to reach `T.field`.

### 8.2 Receiver Coercion

When resolving a method call `x.method(args)`, the compiler tries the following receiver types in order:

1. `T` (direct value)
2. `&T` (shared borrow — insert `&x`)
3. `&mut T` (unique borrow — insert `&mut x`, requires mutable lvalue)

If `x` is a heap reference (`*T` or `*mut T`), it is first coerced to a borrow ([§6.1](#61-implicit-coercion-at-call-sites)), then the receiver search proceeds as above.

This allows methods to be defined with borrow receivers and called on values, stack borrows, and heap references seamlessly.

---

## 9. Static Cycle Prevention

### 9.1 Motivation

Reference counting cannot collect cycles. If object A holds `*B` and object B holds `*A`, neither refcount reaches zero and both leak. Ray prevents this statically.

### 9.2 Type Graph Analysis

The compiler builds a directed graph:

- **Nodes**: type definitions (structs, enums).
- **Edges**: for each field of type `*T` (strong reference), add an edge from the containing type to `T`.
- `id *T` fields are **not** edges in this graph (they are weak references).

### 9.3 Rejection Rule

If the strong-reference type graph contains any **strongly connected component** (SCC) of size > 1, or any self-referential type, the program is rejected with an error.

```ray
// ERROR: cyclic strong references between Node and Tree
struct Node {
    parent: *Tree
    value: int
}

struct Tree {
    root: *Node
}
```

### 9.4 Fix: Use `id *T`

At least one back-edge in any cycle must use `id *T`:

```ray
// OK: Node's parent is a weak reference
struct Node {
    parent: id *Tree                   // weak — does not prevent Tree from being freed
    value: int
}

struct Tree {
    root: *Node
}
```

### 9.5 Error Messages

When a cycle is detected, the error message should:

1. Name all types in the cycle.
2. Show the chain of strong references forming the cycle.
3. Suggest which field(s) could be changed to `id *T` to break the cycle.

```
error: cyclic strong references detected
  ┌─ src/tree.ray:2:5
  │
2 │     parent: *Tree
  │     ^^^^^^^^^^^^^^ Node → Tree (strong)
  ·
7 │     root: *Node
  │     ^^^^^^^^^^^ Tree → Node (strong)
  │
  = help: break the cycle by changing one reference to `id *T`
  = suggestion: parent: id *Tree
```

---

## 10. Cloning

### 10.1 The `Clone` Trait

```ray
trait Clone['a] {
    fn clone(&'a) -> 'a
}
```

Clone takes a shared borrow of a value and returns an independent copy as a **value**. The caller decides where the clone lives:

```ray
shared: *Foo = ...

val = shared.clone()                   // Foo value (on stack)
mut copy = box(shared.clone())         // *mut Foo (new heap allocation, mutable)
independent = freeze(box(shared.clone()))  // *Foo (new independent shared ref)
```

### 10.2 Method Call Resolution

Clone is called as a method. Receiver resolution handles all reference types:

| `x` type             | What happens                       | Result    |
|----------------------|------------------------------------|-----------|
| `x: T` (stack value) | auto-ref to `&T`                   | `T` value |
| `x: &T`              | direct match                       | `T` value |
| `x: &mut T`          | coerce to `&T`                     | `T` value |
| `x: *T`              | coerce to `&T`                     | `T` value |
| `x: *mut T`          | coerce to `&T`                     | `T` value |

In all cases, `x` remains available after the call.

### 10.3 Auto-derived Clone

Since `*mut T` and `&mut T` are disallowed in struct fields, all struct fields are copyable, and Clone is always auto-derivable. The default implementation is **shallow**:

- Value fields: copied.
- `&T` fields: copied (plain pointer copy — no refcount effect).
- `*T` fields: copied (bumps refcount — both point to the same object).
- `id *T` fields: copied (bumps weak refcount).

```ray
// compiler generates for:
// struct Foo { x: int, data: *Bar }

impl Clone[Foo] {
    fn clone(self: &Foo) -> Foo {
        Foo {
            x: self.x,            // copy value
            data: self.data,      // copy *Bar ref (bump refcount) — shallow
        }
    }
}
```

### 10.4 Deep Clone

For deep copies (cloning referenced data recursively), implement Clone manually:

```ray
impl Clone[Foo] {
    fn clone(self: &Foo) -> Foo {
        Foo {
            x: self.x,
            data: freeze(box(self.data.clone())),  // deep: clone the Bar, heap-allocate, share
        }
    }
}
```

---

## 11. Nullability

All reference types are **non-null** by default:

```ray
x: *Point    // always points to a valid Point
y: *mut Foo  // always points to a valid Foo
z: id *Bar   // always points to a valid (possibly freed) Bar
a: &Point    // always points to a valid Point
b: &mut Foo  // always points to a valid Foo
```

For optional references, use `nilable`:

```ray
parent: nilable[*Node] // may be nil
```

The `upgrade` function returns `nilable[*T]` because the referent may have been destroyed.

---

## 12. Summary of Built-in Operations

All of the following are **compiler built-ins** with special ownership semantics that cannot be expressed as regular functions.

| Operation      | Signature                   | Description                                |
|----------------|-----------------------------|--------------------------------------------|
| `new(T)`       | `(type) -> *mut T`          | Zero-initialized heap allocation           |
| `box(expr)`    | `(T) -> *mut T`             | Value-initialized heap allocation          |
| `freeze(x)`    | `(*mut T) -> *T`            | Consume unique ref, produce shared ref     |
| `id(x)`        | `(*T) -> id *T`             | Derive weak/identity ref (non-consuming)   |
| `upgrade(x)`   | `(id *T) -> nilable[*T]`    | Attempt to recover strong ref from weak    |
| `alloc(T, n)`  | `(type, uint) -> rawptr[T]` | Unsafe array/buffer allocation             |

---

## 13. Future Considerations

### 13.1 Interior Mutability

The current model enforces that shared references (`*T`) are always read-only. Future work may introduce compiler-known interior mutability primitives:

- `Cell[T]` — single-threaded mutable container, allows mutation through `*Cell[T]`.
- `Mutex[T]` — thread-safe mutable container, allows mutation through `*Mutex[T]` with lock acquisition.

These would be properties of the **pointee type**, not the reference type. The capability system remains unchanged — `*Cell[T]` is still a "shared, read-only reference to a Cell," but `Cell` itself permits internal mutation.

Design of these primitives is deferred to a separate specification.

### 13.2 Trait Objects & Cycle Detection

The static cycle analysis ([§9](#9-static-cycle-prevention)) operates on concrete type graphs. When trait objects are introduced:

- A field of type `*SomeTrait` could hold any concrete type that implements `SomeTrait`, some of which might reference back to the containing type.
- The cycle checker cannot statically determine this.

Possible approaches:
- Require `id *SomeTrait` for trait-object fields that could participate in cycles (conservative).
- Defer to runtime leak detection for trait-object cycles.
- Introduce trait-level annotations that declare reference topology.

This will be addressed when trait objects are designed.

### 13.3 Concurrency

Ray is single-threaded today. The reference model is designed to extend to multi-threaded execution:

- `*T` and `&T` (shared, read-only) are inherently thread-safe — no data races on immutable data.
- `*mut T` and `&mut T` (unique) are inherently thread-safe — no aliasing means no races.
- Refcount operations (`strong_count`, `weak_count`) should use atomic operations when concurrency is enabled.
- Shared mutation (through future interior mutability primitives) will require synchronization (`Mutex[T]`, atomics).
- A `Send`/`Sync`-like trait system may be introduced to govern which types can cross thread boundaries.

### 13.4 The `Drop` Trait

The name `Drop` is reserved for a future **scope-based** destructor trait, distinct from `Destruct`:

```ray
trait Drop['a] {
    fn drop(*mut 'a)
}
```

- **`Destruct`** ([§4](#4-destructors)): triggered by **refcount** — called when `strong_count` reaches 0. Applies to heap-allocated objects behind `*T` / `*mut T`.
- **`Drop`**: triggered by **scope exit** — called when a value goes out of scope, regardless of how it was allocated. Applies to **any type `T`**, including stack values and value-typed struct fields.

This mirrors Rust's `Drop` trait. A type implementing `Drop` would have its `drop` method called deterministically at scope exit, enabling RAII patterns for file handles, locks, transaction guards, and other resources that aren't heap-allocated references.

**Implication:** types implementing `Drop` would likely need to be **non-copyable**, since implicit copies would create ambiguity about which copy's scope exit triggers the drop. The interaction between `Drop`, copyability, and the struct field rules ([§1.7](#17-unique-references-are-not-allowed-in-struct-fields)) requires careful design.

The exact design is deferred to a separate specification.

### 13.5 Default Trait

A `Default` trait could provide convenience for types that want custom default values beyond zero-initialization:

```ray
trait Default['a] {
    fn default() -> 'a
}
```

This would complement `new(T)` by allowing user-defined defaults. Design is deferred.

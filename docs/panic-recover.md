# Panic & Recover

Ray uses a **flag-based unwinding** model for unrecoverable errors. `panic` signals a fatal error by setting a flag on the thread-local context and returning; callers check the flag after each call to a panicable function and propagate the unwind by returning early. `recover` catches a panic boundary, converting it into a `result` value.

This document is a design specification. It describes the target semantics, not the current implementation.

---

## 1. Surface API

### 1.1 `panic`

```ray
fn panic(msg: string) -> never
```

- Initiates an unwind by setting the context's unwinding flag and storing the message.
- Control never continues past a `panic` call within the panicking function.
- `panic` is a compiler intrinsic.

```ray
fn divide(x: int, y: int) -> int {
    if y == 0 {
        panic("division by zero")
    }
    x / y
}
```

### 1.2 `recover`

```ray
fn recover(body: () -> 'a) -> result['a, string]
```

- Executes `body`. If `body` completes normally, returns `ok(value)`.
- If `body` panics (directly or transitively), catches the panic and returns `err(msg)`.
- `recover` is a compiler intrinsic — the compiler statically knows which frames have recover scopes and emits the appropriate flag-check handling inline.

```ray
res = recover(() => divide(10, 0))
if ok(value) = res {
    puts("result: {value}")
} else if err(msg) = res {
    puts("caught panic: {msg}")
}
```

### 1.3 Prerequisites

`recover` depends on the `result['a, 'e]` enum type and `match`/destructuring support. These are separate language features that must be implemented first.

---

## 2. Thread Context

### 2.1 Structure

The runtime maintains a thread-local context struct in linear memory, accessed via a WASM module-level global pointer. For the current single-threaded target, this is a simple global. For future green threads, each fiber gets its own context.

The panic-relevant fields are:

```
ThreadContext {
    unwinding: bool              // true while a panic is propagating
    panic_message: string        // the panic message
    stack_trace: StackTrace      // unwind trace for diagnostics
}
```

The context may contain additional fields unrelated to panic (e.g., future green thread scheduling state). The panic fields may be flattened into the top-level struct or grouped as a sub-struct — this is an implementation detail.

### 2.2 Stack Trace

The stack trace is a fixed-size flat array of trace entries, plus a write index:

```
StackTrace {
    entries: [TraceEntry; MAX_TRACE_DEPTH]
    count: uint
}

TraceEntry {
    function_name: *const u8     // pointer to static string data
    file: *const u8              // pointer to static string data
    line: uint
}
```

Entries are only written during unwinding — there is **no cost on the happy path**. No shadow stack, no per-call instrumentation.

- The panic site pushes the first entry.
- Each frame that checks the unwind flag and is about to return early pushes an entry before returning.
- When `count` reaches `MAX_TRACE_DEPTH`, further entries are silently dropped.
- The bottom of the trace (where the panic originated) is preserved; the top (outermost frames) is lost on overflow. This is the right tradeoff — the panic origin is the most important diagnostic.

All trace metadata (function name, file, line) is known at compile time and stored as static data. Each entry is just a pointer to static data plus a line number — essentially free to include.

### 2.3 Lifecycle

1. **Normal state**: `unwinding = false`, `stack_trace.count = 0`.
2. **`panic(msg)` called**: sets `unwinding = true`, stores `msg`, pushes the first trace entry (the panic call site), returns to caller.
3. **Caller checks flag**: after returning from a panicable call, the caller checks `unwinding`. If true, pushes a trace entry, runs any scope cleanup, then returns early (propagating the unwind).
4. **`recover` boundary**: the compiler statically knows which frames have recover scopes. After calling `body`, a recover frame checks `unwinding`. If true, it resets `unwinding = false`, retrieves the message and trace, and returns `err(msg)`. If false, returns `ok(value)`.
5. **No `recover` boundary**: the unwind propagates to `_start`/`main`, which prints the trace and terminates the program.

### 2.4 Initialization

The thread context is allocated and initialized at program startup (in `_start` or equivalent), before any user code runs.

---

## 3. Panicable Analysis

### 3.1 Definition

A function is **panicable** if it can transitively reach a `panic` call. The compiler performs a post-LIR call graph analysis to determine which functions are panicable.

### 3.2 Rules

1. Any function that directly calls `panic` is panicable.
2. Any function that calls a panicable function is itself panicable.
3. Indirect calls (function pointers, closures, trait methods) are conservatively assumed panicable.
4. `extern` functions are not panicable (panic does not cross FFI boundaries).

### 3.3 Zero Overhead for Non-Panicable Calls

The analysis produces a set of panicable function IDs. Only call sites to panicable functions receive the post-call flag check. Non-panicable call sites have zero overhead — no flag check, no branch, no trace entry.

---

## 4. Codegen

### 4.1 `panic` Intrinsic

```
fn panic(msg: string) -> never:
    store true      → context.unwinding
    store msg       → context.panic_message
    store 0         → context.stack_trace.count
    push_trace_entry(caller_function, caller_file, caller_line)
    return <zero-value of caller's return type>
```

Despite the `never` return type in the source language, the compiled function returns normally (with a dummy value). The caller is responsible for checking the flag and not using the return value.

### 4.2 Post-Call Flag Check

After every call to a panicable function, the compiler inserts:

```
result = call panicable_fn(args)
if context.unwinding:
    push_trace_entry(this_function, this_file, this_line)
    <run scope cleanup>
    return <zero-value>
```

This is a conditional branch on a single boolean load. Branch prediction makes the non-panic path nearly free.

### 4.3 `recover` Intrinsic

The compiler inlines `recover` at the call site:

```
result = call body()
if context.unwinding:
    msg = load context.panic_message
    trace = load context.stack_trace    // available for diagnostics
    store false → context.unwinding
    store 0     → context.stack_trace.count
    return err(msg)
else:
    return ok(result)
```

`recover` is the only point where `unwinding` is reset to `false`.

### 4.4 Cleanup

When unwinding through a function, any cleanup required for that scope must execute before the early return. This includes:

- Reference count decrements for heap references going out of scope.
- Future: `Drop` trait calls for types implementing scope-based destruction.

The cleanup is the same code that would run on a normal scope exit — the unwind path reuses it.

---

## 5. Test Framework Integration

The primary motivation for panic/recover is the test framework. The test library (`lib/testing`) uses these primitives:

```ray
fn fail(msg: string) {
    panic(msg)
}

fn assert(cond: bool) {
    if !cond {
        fail("assertion failed")
    }
}

fn assert_eq(left: 'a, right: 'a) where Eq['a, 'a], ToStr['a] {
    if !(left == right) {
        fail("expected {left.to_str()}, got {right.to_str()}")
    }
}
```

The test harness uses `recover` to run each test:

```ray
res = recover(() => test_fn())
if ok(_) = res {
    report_pass(name)
} else if err(msg) = res {
    report_fail(name, msg)
}
```

This allows `assert`, `assert_eq`, `fail`, and any future test helpers to be **pure Ray functions** that work across call boundaries — no intrinsics, no special codegen, no `local[0]` flag.

---

## 6. Design Decisions

### 6.1 Why Flag-Based, Not Exception-Based?

- **Target independence**: works on any backend without relying on WASM EH, DWARF unwinding, or platform-specific exception mechanisms.
- **Green thread compatibility**: when Ray introduces green threads with user-space stacks, the flag-based model works without modification — the context is per-fiber.
- **Simplicity**: the codegen is straightforward conditional branches, not complex `invoke`/`landingpad` IR.
- **Predictability**: the unwind path is visible in the generated code — no hidden control flow.
- **Zero happy-path cost**: the only overhead is a branch-predicted flag check after panicable calls. Stack trace entries are only written during unwind.

### 6.2 Why `result`, Not Exceptions?

`recover` returns a `result` value rather than using catch/throw syntax because:

- It makes the recovery boundary explicit — you can see where panics are caught.
- The result can be stored, passed, or destructured like any other value.
- It avoids introducing exception-handling syntax to the language.

### 6.3 `panic` vs. `fail`

`panic` is the language primitive. `fail` is a library function in `testing.ray` that calls `panic`. The distinction exists so that:

- `panic` can be used outside the test framework (e.g., unreachable branches, contract violations).
- `fail` can add test-specific behavior (e.g., formatting) before panicking.

---

## 7. Future Considerations

### 7.1 Structured Panic Payloads

The initial panic payload is `string`. A future version may introduce a structured type:

```ray
struct panic_info {
    message: string
    trace: list[string]
}
```

This would change `recover`'s signature to `(() -> 'a) -> result['a, panic_info]`. The `result` type makes this evolution straightforward.

### 7.2 Nested `recover`

`recover` calls can nest. Each `recover` catches the innermost panic:

```ray
outer = recover(() => {
    inner = recover(() => panic("inner"))
    // inner is err("inner"), outer continues normally
    42
})
// outer is ok(42)
```

This works naturally — the inner `recover` resets `unwinding` before the outer function's flag check runs.

### 7.3 Panic in Destructors

If a `Destruct` implementation panics while already unwinding, the behavior is a **double fault**. Initial implementation: abort the program. Future work may define more nuanced behavior (e.g., chaining panic messages).

### 7.4 Green Threads

Each green thread/fiber gets its own thread context (including panic state). A panic in one fiber does not affect others. If a fiber panics without a `recover` boundary, the scheduler can catch it and propagate the error to the fiber's join handle.

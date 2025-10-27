# Goals

Ray is a WASM-first programming language built for modern web development. Its design is guided by the following goals:

## Web-first
- Target WebAssembly (WASI) as the default runtime.
- Embrace the modern web stack with easy JavaScript and React interop.
- Support "write once, run anywhere" workflows across browser, edge, and server.

## Friendly but powerful
- Prioritize a low-friction, beginner-friendly syntax inspired by Python.
- Use strong static typing with aggressive type inference.
- Enable concise code without losing safety or rigor.

## UI-aware
- Allow building UI components directly in Ray syntax.
- Compile to React-compatible code or leverage interop bridges.
- Avoid reinventing JSX, but support clean and declarative UI definitions.

## Unified CLI
- One CLI for everything: build, run, format, manage packages, and toolchains.
- Plugin architecture for extensibility without fragmentation.

## Syntactic sugar where it helps
- Add language-level sugar for common web development patterns.
- Keep the core syntax minimal and readable.

## Testable and maintainable
- Built-in support for layered testing: unit, integration, and e2e.
- Keep tests modular and easy to organize in separate files.

## Lightweight and scriptable
- Suitable for both full-stack applications and small automation scripts.
- Fast compile-and-run cycle for quick iteration.

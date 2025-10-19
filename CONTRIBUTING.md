# Contributing to Ray

Thanks for taking the time to improve Ray! This document outlines a few
expectations that keep the repository consistent and easy to work in.

## Development workflow

1. **Set up the toolchain**
   - Install the Rust toolchain specified in `rust-toolchain.toml`
   - Run `cargo check` from the repository root to ensure the workspace builds

2. **Formatting**
   - Always run `cargo fmt` after modifying code. This repository relies on the
     default Rust formatter configuration; unformatted changes will be rejected
     by CI.

3. **Testing**
   - Run the relevant test suites before opening a PR (for parser changes,
     `cargo test parser::tests -- --nocapture` is a good starting point).
   - For broader changes, `cargo test` ensures all workspace tests pass.

4. **Documentation**
   - If you add new subsystems or significant behaviour, update the docs under
     `docs/` and/or the README so other contributors (human or AI assistants)
     understand the new flow.

Following these steps keeps the tree healthy and makes collaboration smoother
for everyone.

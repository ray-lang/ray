# Ray CLI Vision and Roadmap

## Overview

The Ray CLI should evolve into the single entry point for every part of the Ray developer experience: bootstrapping toolchains, installing CLI extensions, managing packages, building and running projects, running analyses, and operating the language server. A single binary (`ray`) orchestrates these workflows.

Key principles:

- Organize commands around developer workflows instead of individual services.
- Keep UX consistent across subcommands (flags, logging, JSON output).
- Share configuration, toolchain discovery, and workspace detection across all features.

## Proposed Command Layout

- `ray setup` – Install and manage toolchains, run environment checks.
- `ray ext` – Install, list, update, and remove CLI extensions.
- `ray pkg` – Interface for package management (init, add/remove deps, publish).
- `ray build` – Current build functionality; extend with watch/profile/target controls.
- `ray run` – Build (when needed) and execute binaries or scripts.
- `ray analyze` – Current analysis; extend with ruleset selection, JSON output, and auto-fix.
- `ray lsp` – Manage lifecycle of the integrated LSP (foreground or daemon modes).
- `ray doctor` – Diagnose environment issues and gather support bundles.
- `ray version` / `ray info` – Report tool versions, active toolchains, and environment metadata.

## Command Architecture

- Core binary with subcommand registry; each command is implemented in its own module or plugin.
- Shared configuration loader draws from project manifests and user-level config (`$XDG_CONFIG_HOME/ray/config.toml`).
- Environment context object passes workspace detection, toolchain paths, telemetry state to subcommands.
- Consistent logging, progress reporting, and `--json` machine-readable output across commands.

## Integrating the LSP

- Convert the existing LSP crate into an internal library crate (e.g., `ray-lsp`) consumed by the CLI.
- Provide a CLI adapter that exposes:
  - `ray lsp launch` (default) – Run the server on stdio for editor integration.
  - `ray lsp daemon` – Start supervised background process; write PID/port to cache.
  - `ray lsp stop` / `ray lsp status` – Control commands for the daemon.
- Expose configuration via CLI flags and environment variables (logging, experimental features).
- Share configuration and toolchain metadata with the LSP through common library crates to ensure consistent view of the workspace.
- Add `ray lsp probe` for quick health checks useful to IDE automation.

## Plugin and Extension Strategy

- `ray ext` handles installing, updating, and removing extensions shipped as executables (`ray-ext-<name>`).
- CLI discovers extensions on `PATH` at startup and merges their subcommands into help output.
- Define an extension manifest schema that includes compatibility constraints and required capabilities.
- Consider sandboxing or prompting before running third-party extension commands.

## Toolchain Management (`ray setup`)

- `ray setup install <channel>` installs compiler, standard library, and runtime dependencies for stable/nightly.
- Maintain a local toolchain registry; downloads orchestrated via artifact service or static bundles.
- `ray setup doctor` validates host dependencies and environment.
- `ray setup switch <channel>` switches global defaults; allow per-project overrides in manifests.

## Package Management (`ray pkg`)

- Wrap existing package resolver APIs to offer: `init`, `add`, `remove`, `update`, `publish`, `graph`, `offline`.
- Manage lockfile lifecycle, reproducibility, and vendor mode.
- Provide `--json` outputs for IDE tooling and automation to inspect dependency graphs.

## Build, Run, and Analyze Enhancements

- `ray build`: integrate build caching, incremental rebuilds, cross-compilation targets, and `--emit` options.
- `ray run`: automatically build before running; support `--release`, `--args`, debugging hooks, and remote targets.
- `ray analyze`: unify static analysis, linting, formatting, and security checks; allow configuration via project manifests.

## Diagnostics and Telemetry

- `ray doctor` gathers environment info, logs, and optionally produces shareable support bundles.
- `ray info` outputs versions, toolchain paths, and relevant configuration for automation.
- Telemetry is opt-in and configurable via shared settings.

## Internal Architecture

- Shared crates for `ray-config`, `ray-workspace`, `ray-lsp`, `ray-build`, `ray-analyze`, and `ray-ext`.
- CLI crate remains thin, wiring subcommands to shared services.
- Adopt a shared async runtime (e.g., Tokio) if concurrency primitives are required by LSP or tooling.
- Use trait-based plugin interfaces where internal components may be optional.

## Rollout Plan

1. Refactor LSP crate into reusable library and add `ray lsp launch`.
2. Introduce shared configuration crates consumed by build, analyze, and LSP modules.
3. Implement `setup`, `run`, and `pkg` commands with consistent UX over existing functionality.
4. Add plugin discovery and `ray ext` lifecycle commands.
5. Harden `ray doctor`, telemetry toggles, and machine-readable outputs.
6. Publish CLI specification and developer documentation for extensions and IDE integration.

## Immediate Next Steps

1. Finalize CLI UX and flag naming in a written spec.
2. Inventory existing crates to identify reusable configuration and workspace logic.
3. Draft migration guidance so IDEs launch the LSP via `ray lsp`.

# Evaluate once via Homebrew
LLVM_SYS_170_PREFIX := $(shell brew --prefix llvm@17)
LLVM_SYS_CONFIG_PATH := $(LLVM_SYS_170_PREFIX)/bin/llvm-config

export LLVM_SYS_170_PREFIX
export LLVM_SYS_CONFIG_PATH

.PHONY: build build-backend build-release core dev-toolchain release-toolchain

build: build-backend
	@cargo build

build-backend:
	@cargo build -p ray-backend

build-release:
	@cargo build --release
	@cargo build --release -p ray-backend

core: build
	@mkdir -p .ray/lib/ray
	@target/debug/ray --root-path $(PWD)/.ray build lib/core --lib --no-core

dev-toolchain: build build-backend
	@mkdir -p .ray/bin .ray/lib/ray
	@cp target/debug/ray-backend .ray/bin/ray-backend
	@target/debug/ray --root-path $(PWD)/.ray build lib/core --lib --no-core
	@cp lib/core/.raylib .ray/lib/ray/core.raylib

release-toolchain:
	@echo "==> cargo build --release -p ray-backend"
	@cargo build --release -p ray-backend
	@echo "==> cargo build --release"
	@cargo build --release
	@echo "==> staging toolchain contents"
	@mkdir -p build/toolchain/bin build/toolchain/lib/ray
	@cp target/release/ray-backend build/toolchain/bin/ray-backend
	@target/release/ray --root-path $(PWD)/build/toolchain build lib/core --lib --no-core
	@cp build/toolchain/build/core.raylib build/toolchain/lib/ray/core.raylib
	@echo "==> writing toolchain manifest"
	@printf 'version = "%s"\nchannel = "%s"\ntriple = "%s"\n' "local" "local" "wasm32-wasi" > build/toolchain/manifest.toml
	@echo "==> cleaning staging artifacts"
	@rm -rf build/toolchain/build

# Evaluate once via Homebrew
LLVM_SYS_170_PREFIX := $(shell brew --prefix llvm@17)
LLVM_SYS_CONFIG_PATH := $(LLVM_SYS_170_PREFIX)/bin/llvm-config

export LLVM_SYS_170_PREFIX
export LLVM_SYS_CONFIG_PATH

.PHONY: build build-backend core dev-toolchain

build: build-backend
	@cargo build

build-backend:
	@cargo build -p ray-backend

core: build
	@target/debug/ray --root-path $(PWD)/.ray build lib/core --lib --no-core

dev-toolchain: build build-backend
	@mkdir -p .ray/bin .ray/lib
	@cp target/debug/ray-backend .ray/bin/ray-backend
	@target/debug/ray --root-path $(PWD)/.ray build lib/core --lib --no-core
	@cp lib/core/.raylib .ray/lib/core.raylib

# Evaluate once via Homebrew
LLVM_SYS_170_PREFIX := $(shell brew --prefix llvm@17)
LLVM_SYS_CONFIG_PATH := $(LLVM_SYS_170_PREFIX)/bin/llvm-config

export LLVM_SYS_170_PREFIX
export LLVM_SYS_CONFIG_PATH

.PHONY: build core

build:
	@cargo build

core: build
	@target/debug/ray --root-path $(PWD) build lib/core --lib --no-core

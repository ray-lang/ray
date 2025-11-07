# Evaluate once via Homebrew
LLVM_SYS_170_PREFIX := $(shell brew --prefix llvm@17)
LLVM_SYS_CONFIG_PATH := $(LLVM_SYS_170_PREFIX)/bin/llvm-config

export LLVM_SYS_170_PREFIX
export LLVM_SYS_CONFIG_PATH

.PHONY: build build-release core dev-toolchain release-toolchain

build:
	@cargo build

build-release:
	@cargo build --release

core: build
	@mkdir -p .ray/lib
	@target/debug/ray --root-path $(PWD)/.ray build lib/core --lib --no-core

dev-toolchain: build
	@mkdir -p .ray/lib
	@target/debug/ray --root-path $(PWD)/.ray build lib/core --lib --no-core
	@cp lib/core/.raylib .ray/lib/core.raylib

release-toolchain:
	@echo "==> cargo build --release"
	@cargo build --release
	@echo "==> staging toolchain contents"
	@mkdir -p build/toolchain/lib
	@target/release/ray --root-path $(PWD)/build/toolchain build lib/core --lib --no-core
	@cp build/toolchain/build/core.raylib build/toolchain/lib/core.raylib
	@echo "==> writing toolchain manifest"
	@printf 'version = "%s"\nchannel = "%s"\n' "local" "local" > build/toolchain/manifest.toml
	@echo "==> cleaning staging artifacts"
	@rm -rf build/toolchain/build

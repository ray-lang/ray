# Evaluate once via Homebrew
LLVM_SYS_170_PREFIX := $(shell brew --prefix llvm@17)
LLVM_SYS_CONFIG_PATH := $(LLVM_SYS_170_PREFIX)/bin/llvm-config

export LLVM_SYS_170_PREFIX
export LLVM_SYS_CONFIG_PATH

.PHONY: build build-release core dev-toolchain release-toolchain vscode-ext

build:
	@cargo build

build-release:
	@cargo build --release

lib-core: build
	@mkdir -p .ray/lib
	@target/debug/ray --root-path $(PWD)/.ray --config-path=lib/core/ray.toml build lib/core
	@cp lib/core/.raylib .ray/lib/core.raylib

lib-testing: lib-core
	@target/debug/ray --root-path $(PWD)/.ray --config-path=lib/testing/ray.toml build lib/testing
	@cp lib/testing/.raylib .ray/lib/testing.raylib

dev-toolchain: lib-testing

release-toolchain:
	@echo "==> cargo build --release"
	@cargo build --release
	@echo "==> staging toolchain contents"
	@mkdir -p build/toolchain/lib
	@target/release/ray --root-path $(PWD)/build/toolchain build lib/core --lib --no-core
	@cp lib/core/.raylib build/toolchain/lib/core.raylib
	@target/release/ray --root-path $(PWD)/build/toolchain build lib/testing --lib
	@cp lib/testing/.raylib build/toolchain/lib/testing.raylib
	@echo "==> writing toolchain manifest"
	@printf 'version = "%s"\nchannel = "%s"\n' "local" "local" > build/toolchain/manifest.toml
	@echo "==> cleaning staging artifacts"
	@rm -rf build/toolchain/build

vscode-ext:
	@echo "==> compiling extension from TS"
	@cd editors/vscode && npm run compile
	@echo "==> packaging extension VSIX"
	@cd editors/vscode && vsce package --skip-license

clean:
	@echo "==> clearing .ray/lib"
	@rm -rf .ray/lib
	@echo "==> clearing build caches"
	@rm -rf lib/core/.ray lib/testing/.ray 

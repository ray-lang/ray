LLVM_VERSION := 21.1.8
LLVM_SYS_211_PREFIX := $(CURDIR)/.local/llvm
LLVM_SYS_CONFIG_PATH := $(LLVM_SYS_211_PREFIX)/bin/llvm-config

export LLVM_SYS_211_PREFIX
export LLVM_SYS_CONFIG_PATH

.PHONY: build build-release core dev-toolchain release-toolchain vscode-ext wasi-malloc install-llvm

build:
	@cargo build

build-release:
	@cargo build --release

lib-core: build
	@mkdir -p .ray/lib
	@target/debug/ray --root-path $(PWD)/.ray --config-path=lib/core/ray.toml build lib/core
	@cp lib/core/.ray/build/core.raylib .ray/lib/core.raylib

lib-testing: lib-core
	@target/debug/ray --root-path $(PWD)/.ray --config-path=lib/testing/ray.toml build lib/testing
	@cp lib/testing/.ray/build/testing.raylib .ray/lib/testing.raylib

dev-toolchain: lib-testing

release-toolchain:
	@echo "==> cargo build --release"
	@cargo build --release
	@echo "==> staging toolchain contents"
	@mkdir -p build/toolchain/lib
	@target/release/ray --root-path $(PWD)/build/toolchain build lib/core --lib --no-core
	@cp lib/core/.ray/build/core.raylib build/toolchain/lib/core.raylib
	@target/release/ray --root-path $(PWD)/build/toolchain build lib/testing --lib
	@cp lib/testing/.ray/build/testing.raylib build/toolchain/lib/testing.raylib
	@echo "==> writing toolchain manifest"
	@printf 'version = "%s"\nchannel = "%s"\n' "local" "local" > build/toolchain/manifest.toml

vscode-ext:
	@echo "==> compiling extension from TS"
	@cd editors/vscode && npm run compile
	@echo "==> packaging extension VSIX"
	@cd editors/vscode && vsce package --skip-license

wasi-malloc:
	@scripts/build-wasi-malloc.sh

install-llvm:
	@if [ -d "$(LLVM_SYS_211_PREFIX)/bin" ]; then \
		echo "LLVM already installed at $(LLVM_SYS_211_PREFIX)"; \
		exit 0; \
	fi; \
	case $$(uname -s) in Darwin) PLATFORM=macos;; Linux) PLATFORM=linux;; *) echo "unsupported OS"; exit 1;; esac; \
	case $$(uname -m) in aarch64) ARCH=arm64;; *) ARCH=$$(uname -m);; esac; \
	ASSET="$${PLATFORM}-$${ARCH}-llvm-$(LLVM_VERSION).zip"; \
	URL="https://github.com/ray-lang/llvm-build/releases/download/llvm-$(LLVM_VERSION)/$${ASSET}"; \
	echo "==> downloading $${ASSET}"; \
	mkdir -p .local; \
	curl -fSL -o .local/llvm.zip "$${URL}"; \
	echo "==> extracting to $(LLVM_SYS_211_PREFIX)"; \
	mkdir -p $(LLVM_SYS_211_PREFIX); \
	unzip -qo .local/llvm.zip -d $(LLVM_SYS_211_PREFIX); \
	rm -f .local/llvm.zip; \
	echo "==> LLVM $(LLVM_VERSION) installed"

clean:
	@echo "==> clearing .ray/lib"
	@rm -rf .ray/lib
	@echo "==> clearing build caches"
	@rm -rf lib/core/.ray lib/testing/.ray

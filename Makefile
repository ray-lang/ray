.PHONY: build core

build:
	@cargo build

core: build
	@target/debug/ray --root-path $(PWD) build lib/core --lib --no-core

#!/usr/bin/env bash
set -euo pipefail

# Build the wasi_builtins crate as a relocatable WASM object for linking
# into Ray-compiled programs.

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

RUSTC="${RUSTC:-rustc}"
CARGO="${CARGO:-cargo}"

# --- Probe for a supported WASI target ---
WASI_TARGET=""
for candidate in wasm32-wasip1 wasm32-wasip1-threads wasm32-wasip2; do
    echo "    checking $candidate ..."
    if "$RUSTC" - --crate-name ___ --print=file-names \
        --target "$candidate" --crate-type bin \
        --print=sysroot --print=cfg -Wwarnings \
        </dev/null >/dev/null 2>&1; then
        WASI_TARGET="$candidate"
        break
    fi
done

if [ -z "$WASI_TARGET" ]; then
    echo "error: No supported WASI target found." >&2
    echo "Install a wasm32-wasip* target, e.g.:" >&2
    echo "  rustup target add wasm32-wasip1" >&2
    exit 1
fi

echo "==> building wasi_builtins (target: $WASI_TARGET)"

# --- Build the relocatable .wasm object ---
TARGET_DIR="$PROJECT_DIR/target/wasi-builtins"
cd "$PROJECT_DIR/crates/wasi_builtins"
CARGO_TARGET_DIR="$TARGET_DIR" \
    "$CARGO" rustc \
    --target="$WASI_TARGET" \
    --release \
    -- \
    -C panic=abort \
    -C opt-level=z \
    -C lto=yes \
    -C embed-bitcode=yes \
    -C link-args=--relocatable \
    -C link-args=--no-gc-sections \
    -C link-args=--strip-all

cp "$TARGET_DIR/$WASI_TARGET/release/wasi_builtins.wasm" \
    "$PROJECT_DIR/lib/wasi_builtins/wasi_builtins.wasm"

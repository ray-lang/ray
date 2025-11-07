#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: install-ray.sh [release-tag]

Downloads the Ray CLI binary and toolchain bundle for the current host (darwin/linux, x86_64/arm64)
from the specified GitHub release tag (e.g. nightly-2025-11-06 or v0.2.0), installs the CLI into
${INSTALL_BIN:-$HOME/.local/bin}, and extracts the toolchain into ${RAY_PATH:-$HOME/.ray}.
If no release tag is provided, the latest GitHub release tag is used.
USAGE
}

resolve_latest_tag() {
  echo "==> detecting latest Ray release" >&2
  local api="https://api.github.com/repos/ray-lang/ray/releases/latest"

  local parser=""
  if command -v jq >/dev/null 2>&1; then
    parser="jq"
  elif command -v python3 >/dev/null 2>&1; then
    parser="python3"
  else
    echo "error: python3 or jq is required to auto-detect the latest release (or supply a tag manually)" >&2
    exit 1
  fi

  local tag
  if [[ "$parser" == "jq" ]]; then
    tag=$(curl -fsSL "$api" | jq -r '.tag_name') || true
  else
    tag=$(curl -fsSL "$api" | python3 -c 'import json,sys; print(json.load(sys.stdin)["tag_name"])') || true
  fi

  if [[ -z "${tag:-}" || "$tag" == "null" ]]; then
    echo "error: unable to determine latest release tag; supply one explicitly" >&2
    exit 1
  fi

  echo "$tag"
}

if [[ ${1:-} == "" ]]; then
  RELEASE_TAG=$(resolve_latest_tag)
else
  RELEASE_TAG="$1"
fi
REPO_BASE="https://github.com/ray-lang/ray/releases/download/${RELEASE_TAG}"

HOST_OS=$(uname -s | tr '[:upper:]' '[:lower:]')
case "$HOST_OS" in
  linux|darwin)
    ;;
  *)
    echo "error: unsupported OS '$HOST_OS'" >&2
    exit 1
    ;;
esac

HOST_ARCH=$(uname -m)
case "$HOST_ARCH" in
  x86_64|amd64)
    HOST_ARCH="x86_64"
    ;;
  arm64|aarch64)
    HOST_ARCH="arm64"
    ;;
  *)
    echo "error: unsupported architecture '$HOST_ARCH'" >&2
    exit 1
    ;;
esac

CLI_ASSET="ray-cli-${HOST_OS}-${HOST_ARCH}-${RELEASE_TAG}"
TOOLCHAIN_ASSET="ray-toolchain-${HOST_OS}-${HOST_ARCH}-${RELEASE_TAG}.tar.zst"

TMP_DIR=$(mktemp -d)
cleanup() {
  rm -rf "$TMP_DIR"
}
trap cleanup EXIT

CLI_PATH="$TMP_DIR/${CLI_ASSET}"
TOOLCHAIN_PATH="$TMP_DIR/${TOOLCHAIN_ASSET}"

echo "==> downloading ${CLI_ASSET}" >&2
curl -fsSL "${REPO_BASE}/${CLI_ASSET}" -o "$CLI_PATH"
chmod +x "$CLI_PATH"

echo "==> downloading ${TOOLCHAIN_ASSET}" >&2
curl -fsSL "${REPO_BASE}/${TOOLCHAIN_ASSET}" -o "$TOOLCHAIN_PATH"

RAY_ROOT=${RAY_PATH:-"$HOME/.ray"}
mkdir -p "$RAY_ROOT/bin"

RAY_BIN="$RAY_ROOT/bin/ray"

INSTALL_BIN_DIR=${INSTALL_BIN:-"$HOME/.local/bin"}
mkdir -p "$INSTALL_BIN_DIR"
CLI_TARGET="$INSTALL_BIN_DIR/ray"

echo "==> installing CLI to $RAY_BIN" >&2
cp "$CLI_PATH" "$RAY_BIN"
chmod +x "$RAY_BIN"

echo "==> extracting toolchain into $RAY_ROOT" >&2
if tar --help 2>&1 | grep -q -- '--zstd'; then
  tar --zstd -xf "$TOOLCHAIN_PATH" -C "$RAY_ROOT"
else
  if ! command -v zstd >/dev/null 2>&1; then
    echo "error: tar lacks --zstd support and zstd is not installed" >&2
    exit 1
  fi
  zstd -d "$TOOLCHAIN_PATH" -o "$TMP_DIR/toolchain.tar"
  tar -xf "$TMP_DIR/toolchain.tar" -C "$RAY_ROOT"
fi

echo
echo "Ray installed!" >&2
echo "- CLI:   $RAY_BIN" >&2
echo "- Root:  $RAY_ROOT" >&2
if command -v ln >/dev/null 2>&1; then
  if ln -sf "$RAY_BIN" "$CLI_TARGET"; then
    echo "==> symlinked CLI to $CLI_TARGET" >&2
  else
    echo "warning: unable to create symlink; copying CLI to $CLI_TARGET" >&2
    cp "$RAY_BIN" "$CLI_TARGET"
  fi
else
  echo "warning: 'ln' not found; copying CLI to $CLI_TARGET" >&2
  cp "$RAY_BIN" "$CLI_TARGET"
fi

if [[ ":$PATH:" != *":$INSTALL_BIN_DIR:"* ]]; then
  echo "Add '$INSTALL_BIN_DIR' to your PATH to use 'ray' globally." >&2
fi

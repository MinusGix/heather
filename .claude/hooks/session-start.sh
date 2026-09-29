#!/bin/bash
# SessionStart hook for Claude Code on the web (cloud containers only).
#
# The image's Rust lags stable and the repo pins no toolchain (the compiler
# takes up features as they stabilise, e.g. `if let` guards in 1.95), so
# move to current stable. .cargo/config.toml links with mold, which the image
# does not ship; Ubuntu's archive is reachable through the agent proxy (the
# image's PPAs are not), so apt supplies it. `cargo fetch` warms the registry
# so the container snapshot taken after this hook carries the crates.
# Idempotent: every step is a no-op when already done.
set -euo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

cd "$CLAUDE_PROJECT_DIR"

if ! command -v ld.mold >/dev/null 2>&1; then
  # The image's PPA sources 403 through the proxy; apt-get update still
  # refreshes the Ubuntu archive and exits 0 with warnings.
  apt-get update -qq >/dev/null 2>&1 || true
  DEBIAN_FRONTEND=noninteractive apt-get install -y -qq mold >/dev/null
fi
command -v ld.mold >/dev/null

rustup update stable --no-self-update >/dev/null 2>&1
rustup default stable >/dev/null 2>&1

cargo fetch --quiet

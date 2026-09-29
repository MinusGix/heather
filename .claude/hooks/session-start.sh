#!/bin/bash
# SessionStart hook for Claude Code on the web (cloud containers only).
#
# .cargo/config.toml links with mold, which the cloud image does not ship;
# Ubuntu's archive is reachable through the agent proxy (PPAs are not), so
# apt supplies it. `cargo fetch` warms the registry so the container snapshot
# taken after this hook carries the crates. Idempotent: every step is a no-op
# when already done.
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

cargo fetch --quiet

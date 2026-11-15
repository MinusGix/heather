---
title: One variable to move every suite and gate store out of the checkout
status: closed
labels: [tooling, infrastructure, testing]
area: infrastructure
created: 2026-11-04
updated: 2026-11-04
---

Several checkouts of this repository now run at once: Atelier gives each
implementation thread its own git worktree. Every store the suites and gates
keep was fixed relative to the checkout (`target/semantic-test-images`,
`target/native-test-images`, `target/cli-check-images`, `target/decl-cache`,
and `heather check --cache`'s `.heather/cache`), and none followed
`CARGO_TARGET_DIR`, so each new worktree started every one of them cold.

`HEATHER_CACHE_DIR` now names one directory for all of them:
`heather_cache::store_root` is `$HEATHER_CACHE_DIR` when set, else the
checkout's `target/`; the four suite stores sit beneath it by their old names,
and `heather check --cache` with no `--cache-dir` uses `$HEATHER_CACHE_DIR/check`
(`heather_cache::default_dir`). `scripts/test` seeds into it, the runner's
library-gate probe asks it, and `scripts/sentinel` publishes from it.

Sharing is sound because every store is content-addressed and every replay is
rechecked or vouched for under the reader's own kernel
(`docs/infrastructure/cache-v1-design.md`): a shared store can cost a miss, never a wrong
answer. What sharing *costs* between checkouts whose compilers differ is owned
by [[verdict-store-one-kernel]] and [[image-store-identity-overwrite]].

`CARGO_TARGET_DIR` is a different matter and is not touched here: Cargo
decides freshness of workspace crates by mtime, keyed by their path relative
to the workspace root, so two worktrees on one target directory can run each
other's binaries. Keep Cargo's target per worktree.

## Log

- 2026-11-04: landed with this file (Atelier's worktree lanes asked for it).
  `crates/cli/tests/check.rs`'s `the_cache_dir_variable_moves_the_default_store`
  pins the CLI default; the runner test pins the probe's path.

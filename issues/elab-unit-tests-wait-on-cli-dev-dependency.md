---
title: elab's unit-test compile waits on the heather-cli dev-dependency and is the build's critical path
status: closed
labels: [testing,performance,build]
created: 2026-09-24
updated: 2026-09-24
---

Cargo cannot scope a dev-dependency to one target, so `heather-elab`'s
dev-dependency on `heather-cli` (needed only by `tests/support/mod.rs`,
`tests/showcase_calculator.rs` and the frontend bench) also gates the crate's
own unit-test build: `heather_elab "lib" (test)` waits for elab lib → cli lib
before it starts, and at ~40 s it is the build's critical path
([[rust-edit-loop-build-bound]] owns the timeline). None of the 249 in-crate
`#[test]`s use `heather-cli` or `heather-cache`.

## Plan

Move only the unit tests, not the integration tests (which 147 issues and
dozens of docs cite as `crates/elab/tests/*.rs` and scripts run as
`-p heather-elab --test X`):

- `crates/elab/Cargo.toml`: `[lib] test = false`.
- New package `crates/elab-unit` (`heather-elab-unit`): `[lib] path =
  "../elab/src/lib.rs"`, a distinct lib name, the same dependencies and
  features as elab, no dev-dependencies, `doctest = false`; opt-level 3 like
  elab. `cargo test -p heather-elab-unit --lib` runs the unit tests.
- The one manifest-dir path in elab's sources (`module_delta.rs`'s registry
  lint, `CARGO_MANIFEST_DIR/src`) resolves relative to the source file
  instead.

Expected: the unit-test compile runs beside the elab lib compile, so the
build is max(~40 s, lib + cli + integration links) rather than their sum.

## Log

- 2026-09-24: **Landed as planned.** `crates/elab-unit` (`heather-elab-unit`, lib `heather_elab_unit` at `../elab/src/lib.rs`, no dev-dependencies, opt-level 3); elab's `[lib] test = false`; `module_delta.rs`'s registry lint reads `CARGO_MANIFEST_DIR/../elab/src`, valid from both packages; the runner normalizes `src_path` so the target's label stays `crates/elab/src/lib.rs`. Unit tests: 249 before and after (`scripts/test -p heather-elab-unit --lib`). Same box, same edits as [[rust-edit-loop-build-bound]]: elab body edit build **77 → 53 s**, kernel body edit **61 → 49 s**; the unit-test compile now starts beside the elab lib (t≈4–8 s) instead of after the cli chain. The last unit to finish is now `heather-cli`'s bin tests at the end of the elab → cli → integration chain. Full `scripts/test`: 2922 passed, 0 failed (tests 125 s; the verdict stores were cold after the edit/revert builds).

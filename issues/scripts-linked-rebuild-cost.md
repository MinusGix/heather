---
title: scripts/linked recompiles every export with the debug binary
status: closed
labels: [tooling,native,exports]
area: infrastructure
created: 2026-11-12
updated: 2026-11-12
---

`scripts/linked` builds the debug `heather` and compiles every row of `crates/linked/generated/EXPORTS.tsv` with it, checking each certificate. With `scan_token` among the exports that is minutes, most of it one export, and `--check` (which `native_linked.rs` also does as a native gate) costs the same.

Two cheap things:

- Use the release binary when one is built and newer than the sources (or build it: the release build is what every other direct run uses, CLAUDE.md). A debug evaluator is several times slower on exactly this workload.
- Skip a row whose inputs did not change: the module's image key, the binary's identity and the row are the key; the `.s` and its certificate verdict are the value. `HEATHER_CACHE_DIR` already has the store.

## Done when

`scripts/linked --check` with nothing changed is seconds, and after an edit to one linked module only that module's rows are recompiled.

## Log

- 2026-11-12: Done by PR #578 (on master 2026-11-12): `scripts/linked` compiles with the release binary and does not recompile a row whose binary and import closure are unchanged. PR #551's merge keeps that script and adds its `linked-exports` step after the comparison.

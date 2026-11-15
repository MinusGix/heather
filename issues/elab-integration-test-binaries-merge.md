---
title: Merge elab's 178 integration-test binaries into families
status: closed
labels: [testing,performance,build]
created: 2026-09-24
updated: 2026-09-24
---

`crates/elab/tests/` is 178 integration-test binaries, each statically
linking the whole compiler: 300–320 CPU-s of build per Rust edit and most of
the 14.7 GB of executables in `target/debug/deps`
([[rust-edit-loop-build-bound]] owns the numbers). Merge them into ~10–15
binaries by family (`function_ir_*`, `lib_std_*`, `certgen_*`, `omega_*`, …).

## Constraints the merge must keep

- **Per-process rails.** `scripts/test`'s address-space and CPU rails are per
  process (CLAUDE.md, `scripts/test`); a merged binary must not
  put a family's tests under one rail. Proposed: the runner
  (`scripts/run-test-targets.mjs`) shards a merged binary by module prefix —
  one process per former file, `--exact`-free filter on `module::` — so rails,
  per-process fixtures (`support::library`'s `OnceLock`) and per-target timing
  rows keep today's granularity, and only the link count changes. Coarser
  shards (fixture sharing) are a later, separate choice.
- **Names.** Timing rows, `EXCLUSIVE_TARGETS`, the fast lane's skips and the
  warm-up invocations (`--test semantic_x86_warmup`, …) name targets today.
- Each file's `mod support;` must become one shared `crate::support`, or
  every module gets its own copy (and its own `OnceLock`).

Do after [[elab-unit-tests-wait-on-cli-dev-dependency]].

## Log

- 2026-09-24: Design written: docs/infrastructure/elab-test-families-design.md (families by #[path] with files in place, runner shards a family by module so rails/fixtures/timing labels are unchanged, a pilot family measured before the rest).
- 2026-09-24: Landed per the design: 178 elab test binaries → 13 families (`crates/elab/tests/families/`) + 3 standalone; the runner shards each family by member file, `scripts/test --test <file>` is rewritten to the family, `scripts/check-elab-test-families.mjs` lints the layout. Same edits, same box, `cargo test --workspace --no-run --timings`: elab body edit 37.5 → 29.1 s wall, 263 → 92 unit-s; kernel body edit 28.8 → 9.2 s, 356 → 68 unit-s; elab test executables 8.64 → 0.86 GB. Suite counts unchanged (full 2922, fast 2765).

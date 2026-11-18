---
title: Save the verdict store by appending, not by rewriting a 145 MB file per module
status: closed
labels: [testing, performance, caching]
area: infrastructure
created: 2026-11-17
updated: 2026-11-17
---

The CLI image store's verdict file (`target/cli-check-images/entries-v1.tsv`)
was 145 MB on a fresh cloud container: thirteen kernels' sections, 970K
lines, of which the current kernel's was 154K. `Store::save_at` reads,
parses, verifies and rewrites the whole file, and the library gate's build
workers (`heather check --build-worker`) save after every module they build;
`compile-x86` and the folder checks save once each.

## Measured

4-core cloud box, debug `heather`, cold build of `lib/std/algebra`'s closure
(37 modules, `--build-jobs 4 --build-only`), into an empty store and into one
whose `entries-v1.tsv` held only the other twelve kernels' sections (122 MB,
so no verdict could hit):

| store | wall | CPU (user) |
|---|---|---|
| empty | 14.2 s | 22.7 s |
| 122 MB of other kernels' verdicts, before | 24.2 s | 50.2 s |
| the same, after | 14.2 s | 23.3 s |

About one CPU-second per module built. The whole-library gate in a full
`scripts/test --pr` on a fresh container cost 2824 CPU-s; at ~650 modules and
~45 folder processes this file was on the order of a third of it.

## Change

`crates/cache/src/store.rs`: over a base of at least `JOURNAL_ABOVE_BYTES`
(1 MiB) a save writes only the entries added since its last save, as a
one-section file in `entries-v1.d/`; a reader unions its kernel's sections of
the base and the journal; every `COMPACT_AT_FILES` (64) journal files the
save that finds them folds them into the base under a lock and removes them.
A small store is rewritten whole as before, so the existing format tests are
unchanged. Design: `docs/infrastructure/cache-v1-design.md` §8.

Test: `crates/cache/tests/end_to_end.rs::saves_over_a_large_base_append_a_journal`.

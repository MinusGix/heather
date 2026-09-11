---
title: Attribute expensive generated proofs to declarations and conversion requests
status: closed
labels: [tooling,kernel,elaboration,performance,diagnostics]
created: 2026-09-08
updated: 2026-09-11
---

The reusable callee round (`cb877f2`) repeatedly reached resource failures late
in a large generated certificate. Temporary declaration logging helped locate
the responsible proof, but identifying the expensive conversion still required
manual instrumentation and respelling experiments. A successful integration
then took about 270 seconds; this is an observation, not a timing threshold.

## Acceptance

- Optional bounded diagnostics identify the active generated declaration, source
  provenance when available, and checking phase even when checking fails.
- Attribute costly conversion requests using available fuel, allocation, memo,
  and reduction counters; distinguish mismatch, fuel exhaustion, and other limits.
- Support machine-readable output and bounded summaries of compared terms.
  Do not dump entire dependent terms or require a successful check to report.
- Keep observation separate from judgments, fuel accounting, and cache validity;
  avoid material overhead when disabled.
- Start with the x86 call-summary certificate and one small failing reproducer.
  Exact instrumentation and reporting thresholds remain design work.

## What it assumes from elsewhere

- [[ai-facing-tooling]] owns structured diagnostic conventions.
- [[kernel-failed-conversion-cost]] owns improving false-conversion behavior.
- [[kernel-native-depth-budget]] owns safe refusal before stack overflow.

[[test-target-immediate-outcomes]] separately owns prompt reporting of completed
test failures during a long suite; that does not require checker instrumentation.

## Log

- 2026-09-09: First acceptance item landed: `heather build-x86`/`compile-x86` take `--item-timings <file.tsv>` (crates/cli/src/native.rs), which turns on the elaborator's existing `ItemTiming` collector and writes one row per surface item actually elaborated — module, item, total_ms, kernel_ms, and four value-metric columns that fill in only under the `value-metrics` feature. Off by default and nothing is collected when off; the table is written before a failed certificate's error is reported, so a refused check still attributes. crates/cli/tests/native.rs asserts every declaration of a compile-x86 certificate has a row. Used it the same round on examples/x86-native/reused_callee.hthr (release, one furnace box): 1866 rows, 192.1 s of item time, 140.9 s of it kernel, and byte-fetch declarations 88.6 s of that — the first attribution of this certificate that is not a temporary instrumented build. Still owed by this issue: conversion-request attribution (fuel/memo/reduction counters) and bounded summaries of compared terms.
- 2026-09-10: Second acceptance item (conversion-request attribution) reached through the existing sampler rather than new counters: `--item-timings` on `build-x86`/`compile-x86` now also enables the value-machine counters (so the TSV's last four columns fill) and, under the `value-metrics` feature, writes the `Tc::conv_ty` miss table with its item column beside the TSV as `<file>.conv-miss.txt`; `heather check` under `HEATHER_VALUE_METRICS` prints the same table per module, and its item loop now sets the sampler's item name too (crates/elab/src/lib.rs `check_module_source_inner`), so probe files attribute by declaration. `HEATHER_CONV_MISS_TRACE=<item>` (feature-gated, crates/kernel/src/typing.rs) prints every miss of one item with site and excerpt — the table keeps one excerpt per head pair, which is the library's first miss, not the certificate's. Used the same day to attribute the fetch residue ([[native-summary-test-cpu-margin]]): a certificate's `--item-timings` TSV plus its conv-miss file named the family, a probe with `--cache` replayed the library so the excerpts were the probe's own, and the trace of one fetch level (616 misses) named the site. Caveat learned: with `--cache` the root's declarations are accepted from the declaration cache too, so a metrics run of a probe must not use it (the report is reset per module, so the imports' misses stay out anyway).
- 2026-09-11: Triage 2026-09-11: both acceptance items are in tree (--item-timings TSV on build-x86/compile-x86, the .conv-miss.txt sidecar, the per-module table) and have already attributed three native-summary bites. The one residual sub-item (fuel/memo/reduction counters distinguishing mismatch from fuel exhaustion) moves to [[perf-instrumentation-consolidation]]. Closing.

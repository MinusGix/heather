---
title: Attribute expensive generated proofs to declarations and conversion requests
status: open
labels: [tooling,kernel,elaboration,performance,diagnostics]
created: 2026-09-08
updated: 2026-09-09
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

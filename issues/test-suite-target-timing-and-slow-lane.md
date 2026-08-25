---
title: Attribute test-target time and restore a genuinely fast lane
status: closed
labels: [testing,tooling,performance]
created: 2026-08-25
updated: 2026-08-25
---

At 2,103 tests, plain `scripts/test` takes roughly ten minutes of reported
target execution and about 11–13 minutes wall on the current machine. The
runner previously printed durations without target names, making the slow
set impossible to identify without reconstructing Cargo's target order.
Meanwhile `--fast` skipped only twelve tests and still traversed nearly every
expensive integration binary.

Make attribution part of every run, then move stable exhaustive matrices to
the slow lane while retaining a small load-bearing positive/negative set for
each feature in `--fast`. A test named `slow_acceptance_*` is the explicit
convention: plain runs include it; `--fast` filters it. Do not classify a test
as slow merely because it currently performs badly if it is the only
high-signal regression for an active implementation seam.

## Acceptance

- Every `scripts/test` invocation prints the slowest named targets, summed
  reported target time, and compile/test/total runner wall time.
- The table remains trustworthy on ordinary failures and killed binaries.
- Targets above 15 seconds get a recorded attribution or an explicit
  slow-lane decision.
- `--fast` retains representative generated-term positives and negative
  controls while dropping stable cross-products and whole-library repetition.
- Measure the full fast lane and close with before/after wall and test counts.

## What it assumes from elsewhere

- **[[parallel-test-target-execution]]** owns running independent binaries
  concurrently; this issue measures the serial baseline and lane contents.
- **[[integration-test-prefix-reelaboration]]** owns eliminating repeated
  library/prelude setup rather than filtering its consequences.

## Log

- 2026-08-25: First attribution batch: `lib_algebra` 67.30 s,
  `reprgen` 42.11 s, `lib_std_list` 7.30 s, `indexed_route_2b` 0.31 s, and
  fast-filtered `ir_v1` 0.52 s. Replaying the unchanged seven-module algebra
  prefix while keeping one ungated acceptance cut `lib_algebra` to 29.32 s
  cold / 27.61 s warm. Its 31 stable matrix probes and reprgen's 34 hand-run
  matrix probes now use the `slow_acceptance_` convention; four load-bearing
  tests remain fast in each target.
- 2026-08-25: Second batch found `lib_std_bitvec` 41.91 s, `nat_order`
  27.22 s, and `lib_std_int` 16.56 s; the comparison targets were
  `lib_std_tree` 9.81 s, `lib_list_algos` 5.21 s, `nat_arith` 1.21 s,
  `nat_parity` 0.78 s, and `tier1_list_proofs` 0.04 s. Verdict replay cut
  the first three to 20.07 / 12.36 / 7.77 s and left the module-checking
  backstop ungated. Bitvec's three closed computational cross-products moved
  to the slow lane; its module, open-width, and open-law tests remain fast at
  9.78 s. Across algebra/reprgen/bitvec, 68 stable matrix tests moved out of
  `--fast`; their retained slices take about 26 s instead of 91 s, while a
  plain selected-target run still passes all 103 tests.
- 2026-08-25: Closed after the snapshot-fixture and bounded-parallel rounds.
  A warm `scripts/test --fast` run at the automatic six-job bound passes
  1,973 tests in 63 seconds, down from 2,024 tests in 80 seconds at seven
  jobs before the final 51 stable matrix cases moved to the slow lane. The
  retained four-test slices for `operators_onto_classes`,
  `binder_symbol_notation`, `operation_indexed_classes`, and `lib_algebra`
  all remain fast and load-bearing. Plain `scripts/test` still passes all
  2,103 tests in 134 seconds; its wall time is statistically flat against the
  preceding 131-second run because six-way execution already overlaps the
  saved fixture work.

  The fast lane now has a single serial critical path: `ir_pass_fuel` takes
  60.72 seconds under suite contention and the suite takes 63 seconds. Its
  phase attribution and next work live in [[ir-pass-probe-elaboration-cost]].
  The remaining full-lane targets above fifteen seconds are accounted for by
  [[certgen-harness-cost]], [[record-projection-defs-declaration-cost]], this
  issue's explicit slow-lane decisions, or
  [[integration-test-prefix-reelaboration]]. Further wins therefore belong to
  those production and cross-binary mechanisms rather than more runner or
  lane bookkeeping.

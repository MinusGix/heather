---
title: The fast lane's wall clock is guarded_read's four layout declarations (6–13 s each, all kernel gate)
status: open
labels: [performance,testing,x86,kernel]
created: 2026-09-23
updated: 2026-09-23
---

The fast lane's wall clock is one test, and that test is four declarations.
Per-test times (runner, 2026-09-23) and the suite-wide declaration rows
(`HEATHER_SUITE_DECLS=1`) show:

- The fast lane runs in ~70 s wall at 7-way parallelism;
  `function_ir_guarded_read::selected_bounds_read_checks_and_executes` alone
  takes 68 s, so it is the critical path.
- Of its 68 s, 67 s is inside declarations, and most of that is four
  generated layout declarations, all ~99 % kernel gate:

| declaration | seconds |
|---|---|
| `identity_selected::whole_layout` | 13.5 |
| `identity_selected::branch_layout` | 12.4 |
| `masked_selected::branch_layout` | 10.3 |
| `masked_selected::whole_layout` | 5.8 |

(`x86_64_structured_block` re-elaborated in it is another 2.3 s —
[[suite-tests-reelaborate-library-modules]].)

The next heaviest single declarations in the lane, for scale:
`ir_v1::constant_match_fusion_letcon_law_probe` 10.1 s (one test),
`x86_64_access_code::access_sequence` 4.9 s over two tests.

Question before any fix: the layouts are proofs about concrete byte
sequences of the guarded-read branch (`AccessFragment::branch` in the test) —
is the gate evaluating the whole encoded layout per proof (so cost ∝ bytes ×
something), and do `whole_layout` and `branch_layout` re-derive the same
facts? Same shape as [[x86-block-linked-conditional-evaluation-cost]]
(millions of steps, genuine evaluation, few misses) — check the step and
miss columns in the per-test table
(`target/suite-decls-fast/function_ir_guarded_read.*.tsv`, readable with
`scripts/timings`).

Payoff: halving these four roughly halves the fast lane's wall clock, since
the next-longest test is ~35 s (`showcase::cli_tier_showcases_check`).

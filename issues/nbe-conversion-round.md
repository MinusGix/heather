---
title: Execute the shared-value whnf plan (nbe-conversion-design §13)
status: open
labels: [kernel,conversion,performance,meta]
created: 2026-07-31
updated: 2026-07-31
---

Execution tracker for the sharing-preserving conversion round. The
*design* lives in `docs/nbe-conversion-design.md` (decided answers,
rejected alternatives, §13 staged plan) and is not restated here; the
*defect* is owned by [[whnf-sharing-term-growth]] (which closes only when
the acceptance instrument goes linear). This issue owns stage status:
each stage logs its landing, gate results, and any deviation from the
doc here.

## Stages (design doc §13; sizes in definitions-rounds)

| stage | what | size | status |
| --- | --- | --- | --- |
| 0 | acceptance instrument: elaborated arm-nested probe, CLI-level, validated ≥1.8×/level ON MASTER | 0.3 | pending |
| 1 | value domain + evaluator, unwired, differential-tested against the rewriter over `wt.rs` streams | 1.5 | pending |
| 2a | conversion arms made shape-agnostic (accessor trait), zero behavior change | 0.7 | pending |
| 2b | conversion switched to values (THE risky stage) | 1.5 | pending |
| 3 | δ glueing: memoized unfolds, per-GlobalVar rescoped-body cache | 0.7 | pending |
| 4 | cleanup: DESIGN.md rewording, bounds.rs re-measured (prediction: conversion's 21% leaves entirely) | 0.5 | pending |

## Standing gates (every stage)

- `scripts/test` fully green; `scripts/bench --check` clean.
- Every direct `heather` run under the ulimit rail (CLAUDE.md).
- Stage 2b additionally: the stage-0 instrument goes exponential→linear,
  routine `lib/ir_v1.hthr` does not regress, and the differential suite
  (rewriter vs evaluator) is green across ≥4 seed streams.

## Kill criteria

- Stage 0: no probe reaches ≥1.8×/level on master ⇒ STOP the round,
  reopen diagnosis on [[whnf-sharing-term-growth]] — the fix would be
  unfalsifiable without the instrument.
- Stage 2b: a conversion-vs-conversion disagreement not traced to a
  *rewriter* bug within one session ⇒ revert to master, re-scope; the
  stage-1 evaluator keeps its value as an oracle-side artifact.

## Log

- 2026-07-31: Filed as the execution tracker after the design round landed (b35a18f, 52a6ecf). Stage 0 dispatched first and separately, per the design round's recommendation: the spike showed hand-built kernel probes stay linear (small-term pointer sharing via the depth-zero fast path), so the instrument must be validated on master before any evaluator code is funded.

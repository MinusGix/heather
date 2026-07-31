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
| 0 | acceptance instrument: elaborated arm-nested probe, CLI-level, validated ≥1.8×/level ON MASTER | 0.3 | **done** (`scripts/probe-whnf-sharing`) |
| 1 | value domain + evaluator, unwired, differential-tested against the rewriter over `wt.rs` streams | 1.5 | pending |
| 2a | conversion arms made shape-agnostic (accessor trait), zero behavior change | 0.7 | pending |
| 2b | conversion switched to values (THE risky stage) | 1.5 | pending |
| 3 | δ glueing: memoized unfolds, per-GlobalVar rescoped-body cache | 0.7 | pending |
| 4 | cleanup: DESIGN.md rewording, bounds.rs re-measured (prediction: conversion's 21% leaves entirely) | 0.5 | pending |

## Standing gates (every stage)

- `scripts/test` fully green; `scripts/bench --check` clean.
- Every direct `heather` run under the ulimit rail (CLAUDE.md).
- Stage 2b additionally: the stage-0 instrument goes exponential→linear —
  concretely, `scripts/probe-whnf-sharing --max 15 --family both --expect
  linear` exits zero, run on the same machine as the master curve recorded in
  that script's docstring,
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
- 2026-07-31: **Stage 0 landed and the kill criterion did NOT fire.** The instrument is `scripts/probe-whnf-sharing` (python3, stdlib only, `scripts/issue`'s precedent), deliberately outside both `scripts/test` and `scripts/bench`: a wall-clock threshold in a test rots, the assertion is the ratio between adjacent levels, and §12 already established that this shape cannot be a kernel bench. It generates probe files rather than committing them — each is `lib/ir_v1.hthr`'s declarations (the same cut `crates/elab/tests/ir_v1.rs` makes; there is no import system) plus one generated theorem — so the probe tracks the library instead of drifting from a copy. Every run is under the CLAUDE.md rail, as `resource.setrlimit` on the child; `os.wait4` gives per-run peak RSS. Master curve at 4300b31, baseline-subtracted, N = 1..15: wall 0.06s → 33.77s, peak RSS 0.0 MB → 4544 MB. **Gate held on both quantities**: RSS ratio ≥ 1.8 across five consecutive levels (N = 11..15) with tail geometric mean 2.12, wall three consecutive (N = 10..12, with 13 at 1.79) and tail geometric mean 1.91 — per-level wall ratios wander ±30% with machine load across repeat sweeps, so the geometric mean is the statistic and the run is its sanity check. The negative control (`--family flat`: identical nesting, nothing consuming the nested eval's payload) never reaches 1.8 anywhere and is ~0.04 s / ~0.4 MB per level. N = 15 is the last level under the 8 GB cap. The sweep also sharpened the diagnosis, which is why three variants were built and not one: nesting alone is NOT the axis (13 MB at N=12), nor is a scrutinee value that deepens per level (13 MB), and what multiplies is the pending continuation REBINDING the nested eval's `Out` payload (511 MB) — the issue's surviving hypothesis, isolated in-language. The optional kernel-bench variant was attempted (family D in design §12: the carried argument duplicated at binder depth 1, where `subst.rs`'s own doc says the fast path cannot share it) and measured **linear**, slope 1.44 over twelve levels; it is not the gate, and four hand-built families have now failed where the elaborated probe succeeds. Stages 1 and 2a are unblocked.

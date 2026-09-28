---
title: Conjunction field chains still traverse their remaining types during elaboration
status: closed
labels: [elaboration,performance,proofs]
created: 2026-09-28
updated: 2026-09-28
---

The kernel prefix replay is fixed by [[conjunction-projection-chain-cost]],
whose evaluator-step family is now linear. Source checking remains
superlinear: field preparation substitutes through the remaining structural
tail and spells the selected field at every source dot. A selected `.right`
field is itself the next large conjunction, so those traversals overlap.

Reproduce with `probes/conjunction_projection_chain.py`; compare using
`scripts/perf ab --file target/conjunction-chain.hthr:lib/std` and inspect
`decl_body_ns` separately from the kernel gate. Keep the bare-parameter and
opaque-theorem-alias variants, open element types and dependent-field controls.

On 2026-09-28, the post-fix bare family at depths 8/16/32/64 has evaluator
steps 84/180/372/756 but `shift_global_nodes` 1667/7067/29387/120107. Those
rescoping counts include elaboration's naming probes as well as the gate;
they are not a kernel-only counter. The source-side type walks still dominate
large items. The measured A/B was under host load, so it establishes exact
counter shapes, not a clean wall-time exponent.

Investigate whether carrying structural type components with deferred local
substitution can avoid re-traversing the suffix. Do not widen named-projection
receiver policy without the controls owned by
[[per-instantiation-projection-boundaries]].

## Acceptance

Attribute the remaining structural substitution, emission and instance-matching
traversals separately, then reduce their repeated work on this family without
changing field identity or dependent substitution. Measure a current library
customer as well as the synthetic chain before choosing a representation change.

## Log

### 2026-09-28 — keep checked field inference structural

Added `projection_subst_ns`, `projection_emit_ns`, `instance_match_ns`,
`projection_named`, `projection_structural` and `instance_match_calls`.
An instrumented pre-fix binary attributed the selected field's
`annotation_type` call separately from dependent tail substitution. Timers
are exclusive: nested instance matching owns its time, so a small emission
self time does not mean emission's recursive work is small. Matching recovers
arguments, validates the instance by strict identity, then emits its arguments
recursively. A selected conjunction suffix repeats that work at every dot.
The decline trace showed receiver-gate declines, not failed instance recovery;
widening the gate would address a different problem.

`project_field` now returns the checked projection's structural `fst` type
directly, matching the existing annotation-component design's rule for
structural reads. Callers still emit annotations through the normal emission
boundary. Component projections inside quotations retain their parallel
emission walk. There is no new type representation or receiver policy.

Three interleaved, cold, width-one samples through `scripts/perf ab` compared
the instrumented pre-fix compiler (SHA-256 prefix `049634f7dad5`) with the fix
(`50b088ff99b0`). Exact per-item counts:

| Item | Instance matches before → after | Kernel steps before → after |
| --- | --- | --- |
| bare depths 8/16/32/64 | 30/122/498/2018 → 15/31/63/127 | 84/180/372/756, unchanged |
| alias depths 8/16/32/64 | 44/152/560/2144 → 16/32/64/128 | 96/192/384/768, unchanged |
| `decimal_line::line_word_value` | 545 → 0 | 1664, unchanged |

Projection routes are unchanged too: one named read and `k−1` structural
reads for bare depth `k`, zero named and `k` structural reads for its opaque
alias; the current library theorem still has 72 structural reads. Its global
rescoping node count falls from 42,968 to 10,268. The regression in
`annotation_cost.rs` bounds both kernel steps and instance-match growth and
asserts that aliases retain the structural route. Existing open, dependent,
literal, neutral and wrong-field/value controls remain.

The attribution report and raw rows are saved at
`target/projection-prep/attribution-ab.json` and
`target/projection-prep/attribution-raw` (untracked). The harness warned about
host load; seconds from this round do not establish a stable speedup or
wall-time exponent.

A second three-sample harness run built the before compiler from `b09f6f3f`
and asserted `--marker instance_match_calls`: before `a969802cb6bf`, after
`3191cbeeb901`, with the added columns present only in after. It covered the
same family and library customer plus `calc_parser`. The final replayable
report is `target/perf-ab/conjunction-projection-type-preparation.json`;
`target/projection-prep/final-raw` preserves its rows separately from the
instrumented comparison. The named/structural split is established by the
instrumented run; the committed-before run confirms the evaluator and
rescoping changes against the actual parent. Both runs warned about load.

To reproduce the library customer, supply `lib/std`, `lib` and an import
overlay as `-L` roots. The overlay copies `lib/std/bitvec/{nat,omega}.hthr` to
`{bitvec_nat,bitvec_omega}.hthr`, and `lib/std/arch/x86_64/*.hthr` to
`x86_64_<stem>.hthr` except `model.hthr` becomes `x86_64.hthr`. Use copies:
the CLI canonicalizes symlinks before deriving module names. The A/B command
adds `--file lib/decimal_line.hthr:lib/std,lib,<overlay>` to the generated
family's `--file`, with `--samples 3 --kernel-workers 1`.

Decision: retain ordinary structural tail substitution. Its overlapping
suffix traversals, and argument traversal inside the remaining instance
matches, can still cost quadratic source work. This round eliminates the
repeated emission layer; it promises linear match-call and evaluator counts,
not linear end-to-end source checking. A deferred-substitution representation
is not required for this issue's acceptance and is not deferred work owed by
this change.

Validation: focused `annotation_cost` tests **5 passed**; final plain full
`scripts/test` **3,060 passed, 0 failed, 5 ignored**. The sandbox initially
refused a test-binary spawn with `EPERM`; the completed full run used the
same capped script outside that sandbox. `scripts/bench --check` was repeated
after the suite finished: only the pre-existing `wf/check-tree` lower slope
band remains (0.80 against 0.85–1.35, also present in the preceding round).
This change touches no kernel code; additional flags in the overlapping
first run did not repeat. Issue links and index check pass, with the unrelated
existing `fn-recursion-means-the-function` landed/open warning.

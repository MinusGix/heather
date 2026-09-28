---
title: A case step at a BitVec(64) result costs in proportion to the width
status: closed
labels: [kernel,performance,x86,certificates]
created: 2026-09-25
updated: 2026-09-28
---

## Original report (2026-09-25)

A `match` on a Nat literal whose result type is `BitVec(64)` costs about 1.3K
evaluator steps per `Succ` it peels, whatever the arms hold. A plain nested
Nat match with a `Nat` result costs 2 steps per level, and the same lookup at
`BitVec(1)` about 230. So the cost follows the result type's width, not the
work: something materialises `BitVec(width)` (a 64-deep Σ chain) at every case
step.

Measured 2026-09-25 while making composed certificates scale
(`docs/native-first-program-design.md` §10.1), with `probes/dec/lookup*.hthr`
(untracked). A valuation `λ width id => match id { Zero => …, Succ(id_1) => … }`
looked up at id 51 costs 67 710 steps, at id 200 costs 262 006, and at id 0
costs 65. Replacing the arms with neutral `values(width, 0)` changes nothing.

Every generated `_valuation` in the structured and loop certificates has this
shape, so a lookup of port `k` costs about `1.3K × k` steps, and port ids reach
the hundreds in a long body. The crossing carries in `structured_cert.rs`
dispatch with `Nat::leb` over their few entries instead (flat, about 23K per
lookup), which is a workaround at one site, not the fix.

## Acceptance

- Attribute the per-step cost: which evaluation of the motive or result type
  happens per case step, and why its width matters.
- Either the kernel stops paying it (a lazy motive, or not re-evaluating a
  closed result type per step), or the generators use a lookup whose cost does
  not grow with the id. Say which, on evidence.
- A bench family or test pinning the per-step cost flat in the id.

## Log

- 2026-09-25: The structured generator's valuations now avoid the cost (`valuation_body` in `structured_cert.rs`). They dispatch on the id through a balanced `Nat::leb` tree, so a lookup costs a logarithmic number of comparisons, not a step per `Succ`. The kernel cost itself remains, and so does the bench pinning it.
- 2026-09-25: The same round's other residue, the per-link cost in depth, is owned by [[crossing-link-quadratic-cost]].

### 2026-09-28 — decline unrelated neutral steps before reading the motive

Reproduced on `6fa7550a`. The original `probes/dec/lookup4.hthr` neutral
lookup at width 64, id 51 still takes **17,609 evaluator steps**, despite
the intervening reductions from the original report's 67,710.

Attribution: `Eval::fold_run` first declines the Nat algebra, then calls
`fold_transduce`. Its `probe_transducer` previously called `walk_motive`
before inspecting the step's result. That instantiates the motive at a
neutral successor, unfolds the result type, and searches it for a vector.
The word-output probe rejects a neutral lookup value, but the finite-output
fallback then enumerates the result's Sigma spine (bounded by enumeration
depth and state count). Vector width and the Bool/record type codes determine
how much work happens before rejection. Every nested case has fresh step
and motive closures, so memoizing a negative class cannot share that work
across the dispatch chain. The ordinary case evaluator itself never reads
the motive while firing the selected branch.

The classifier now evaluates the step first with neutral predecessor and
recursive-result variables. If it returns a neutral whose head is unrelated
to the recursive result, it declines before inspecting the motive. Such a
head cannot become a recognized producer or consumer after applying more
arguments. Functions, constructors and recursive-result-headed elimination
spines continue through the existing classifier, retaining word producers,
pass steps, finite consumers and scaled consumers. This changes a negative
classification's cost; it neither invents a class nor changes case reduction.

Three interleaved cold `scripts/perf ab` samples at one kernel worker compare
before binary SHA-256 prefix `8edbacbdedde` with after `5d58974bdebc`.
All samples agree on the counters. The public BitVec family uses distinct
neutral ports at every arm:

| Width | ids 0 / 8 / 51 / 200 before | ids 0 / 8 / 51 / 200 after |
| --- | --- | --- |
| 1 | 11 / 43 / 215 / 811 | 11 / 27 / 113 / 411 |
| 8 | 11 / 99 / 572 / 2,211 | 11 / 27 / 113 / 411 |
| 64 | 11 / 187 / 1,133 / 4,411 | 11 / 27 / 113 / 411 |

The original imported Valuation reproduction falls **17,609 → 167 steps**;
delta steps fall **5,121 → 21**. Its fixed overhead differs from the small
family, while the case increment is the same. The A/B harness warned about
host load and wall-time samples overlap: this round establishes evaluator
counts, without claiming a stable wall-time speedup.

Raw rows are saved under `target/valuation-lookup/ab-raw`, with the parked
binaries and generated family beside them. The replayable report is
`target/perf-ab/valuation-lookup-case-step-cost.json` (all untracked).
Reproduce with `scripts/perf ab --base 6fa7550a --only valuation-lookup
--file target/valuation-lookup/family.hthr:lib/std
--file probes/dec/lookup4.hthr:lib/std,lib --samples 3 --kernel-workers 1`.

Regressions in `annotation_cost.rs` and `lib_std_bitvec.rs` pin **two steps
per successor**, independent of closed result width, with a public-library
probe also at an open width and id 200. Distinct ports, the default arm at
ids 201 and 250, explicit successor syntax and wrong-port refusals cover
dispatch semantics. The fix is in the kernel; balanced `Nat::leb` dispatch
in the generators is retained. Total nested dispatch remains linear in the
selected id, with a constant per-step cost rather than repeated word-type
preparation.

Validation: final plain `scripts/test` **3,062 passed, 0 failed, 5 ignored**,
including both new regressions and all classifier/bitvector controls. The
sandbox refused a test-binary spawn with `EPERM`; the completed full run
used the same resource-capped script outside that sandbox. After the suite
finished, `scripts/bench --check` reported only the existing `wf/check-tree`
lower slope-band flag (0.79 against 0.85–1.35, also present before this round).
The overlapping first benchmark's other timing flags did not repeat. No
baseline or band was changed. Issue links and generated index check pass,
with the unrelated existing `fn-recursion-means-the-function` warning.

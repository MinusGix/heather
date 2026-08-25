---
title: Attribute and reduce certified IR-pass probe elaboration cost
status: open
labels: [elaborator,kernel,performance,testing]
created: 2026-08-25
updated: 2026-08-25
---

`crates/elab/tests/ir_pass_fuel.rs` is the longest irreducible fast-lane test:
one test, about 36 seconds standalone and 66–69 seconds under seven-way suite
contention. This is not repeated fixture setup. Temporary phase timing on a
warm debug build attributed 35.76 seconds as follows:

- prelude plus `logic`/`bool`/`nat` and the `ir_v1` declarations: 0.37s;
- initial `PROBE` elaboration: 32.20s;
- the explicit second `check_term(..., DEFAULT_FUEL)` that the test exists to
  pin: 2.30s;
- all three mutated refusal controls together: 0.89s.

A temporary timing `KernelGate` then attributed the largest real gate checks
inside `PROBE`: `constant_match_fusion_letcon_law_probe` 8.80s,
`ir_fold_same_probe` 4.01s, `constant_match_fusion_laws_probe` 3.11s,
`add_default_arm_laws_probe` 2.28s, and `normalize_tags_laws_probe` 1.75s.
Roughly twelve further seconds occur between gate calls in surface elaboration
and term construction. The timing instrumentation was removed after the run.

This deserves production-level attribution of those five terms: term sizes,
conversion/evaluation counters, and whether repeated record projection or
large dependent-law instantiation is rebuilding equivalent syntax. Do not
solve it by raising fuel or moving the one load-bearing test to the slow lane;
it is specifically the compiler-scale default-fuel regression. The likely
customer is the certified-pass/library design, not the test runner.

## Acceptance

- Attribute the top five declarations across elaboration, type checking, and
  term checking with a reusable counter or benchmark rather than committed
  wall-clock assertions.
- Identify the repeated term shape responsible for the ~8.8s letcon-law gate
  and the ~12s pre-gate residual.
- Preserve the explicit default-fuel check and all three mutation controls.
- Cut the standalone target materially without changing kernel fuel policy,
  or record why this is the intended cost of the theorem being pinned.

## Log

- 2026-08-25: The residual is **emitted core mass**, not repeated fixture
  setup or a superlinear kernel path. Temporary per-gate counters and exact
  streaming renders (all instrumentation reverted) measured the five large
  declarations as follows:

  | declaration | exact body rendering | exact type rendering | conversion nodes | evaluator runs / steps |
  |---|---:|---:|---:|---:|
  | `ir_fold_same_probe` | 31.45 MB | 0.46 MB | 7.93 M | 29.80 M / 1.99 M |
  | `normalize_tags_laws_probe` | 20.74 MB | 1.00 MB | 3.40 M | 12.63 M / 0.69 M |
  | `add_default_arm_laws_probe` | 9.92 MB | 1.00 MB | 4.47 M | 17.41 M / 0.67 M |
  | `constant_match_fusion_letcon_law_probe` | 21.71 MB | 0.02 MB | 12.58 M | 49.06 M / 2.44 M |
  | `constant_match_fusion_laws_probe` | 32.28 MB | 1.00 MB | 6.10 M | 23.31 M / 0.75 M |

  The exact sizes are rendered bytes, not node counts, but they expose what
  bounded `Debug` hid: a source declaration of a few dozen lines can carry
  tens of megabytes of fully explicit core annotations. Kernel work tracks
  that mass in the same linear shape already established by
  [[wf-field-conversion-cost]]. The two sources are (1) dependent matches on
  the eight-constructor `Ir`, whose Wf lowering is large, and (2) open
  instantiations of `IrPassLawsProbe<M>(R, alg)`, whose result type alone is
  about one megabyte and is copied through record construction/projection
  annotations.

  Three discriminating experiments were negative. Splitting the nested
  fusion proof at theorem boundaries merely moved the work to the helper
  declarations. Making the law bundles opaque theorems, or binding one
  bundle with a local `let`, did not shrink annotations already emitted into
  the body. A value-domain shortcut for memoized/delta-finished WHNFs roughly
  halved evaluator constructions but left an instrumentation-free standalone
  run at 36.36 seconds against the existing 35.76--36.15-second envelope;
  evaluator construction is not the wall.

  The actionable mechanism is therefore annotation naming/respelling, not a
  checker cache or a test rewrite. [[unnameable-annotation-occurrences]] now
  records this triggered customer: generated type-code definitions currently
  cover closed family types, while these parameterized/value-indexed record
  instantiations remain inline. Preserve this test unchanged until that
  mechanism can shrink the core it produces.

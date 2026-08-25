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

---
title: Reify structural Nat order goals instead of guessing leaf lemmas
status: closed
labels: [proofs,elaboration,metaprogramming,performance,stdlib]
created: 2026-08-26
updated: 2026-08-26
---

The bounded Boolean `arith` slice closes the carry truth table, but it finds
each structural order lemma by speculative enumeration. Across the eight
branches of `carry_threshold`, it clones the elaborator, infers a candidate,
and converts its result type 20 times. The emitted proof is already optimal by
the evaluator counters—exactly the same 20,941 term closures as the handwritten
match—but representative end-to-end time remains roughly 24 ms versus 9 ms,
while both final kernel gates take about 5 ms. The residual cost is search, not
certificate checking.

Reify the small structural order fragment exposed after Boolean reduction and
select its certificate directly. The first useful shapes are the even/odd
doubling reflections represented by `nat::twice_le_twice_iff` and
`nat::twice_le_succ_twice_iff`, including a structural successor on the right.
Selection must follow from the normalized goal shape, not from the number or
ordering of Boolean branches and not from hard-coded knowledge of majority.

This remains an untrusted reconstructor. It emits an ordinary lemma
application, and the completed proof passes the ordinary declaration kernel
gate. A bad reifier may refuse or select a rejected certificate; it cannot make
a false theorem pass.

Acceptance:

- `carry_threshold` uses one deterministic selection per reachable leaf rather
  than 20 speculative probes; the audit report distinguishes direct order
  reification from fallback search.
- The generated and handwritten truth tables retain identical evaluator
  metrics and zero cache eviction.
- A benchmark or diagnostic profile attributes total time, search time, and
  final-gate time separately; wall time is reported rather than used as a noisy
  unit-test assertion.
- Mutating `carry_majority` is still rejected, and opaque terms such as
  `pow(2,n)` are never normalized merely to classify the order goal.
- Unsupported residual inequalities return structured failure state. Broader
  Presburger reasoning is not silently smuggled into this slice.

## What it assumes from elsewhere

- **[[certifying-arithmetic-proof-automation]]** owns the `arith` surface,
  audit/failure interface, and carry acceptance customer. This issue owns only
  structural order-goal recognition and selection.
- **[[grind-port]]** owns eventual general search orchestration. This issue
  should expose a deterministic component that can later participate in it.

## Log

- 2026-08-26: Filed after separating evaluator counts from wall time. Removing
  duplicate speculative proof-term kernel checks made the generated and
  handwritten certificate counts identical, revealing 20 infer/convert probes
  as the remaining Boolean-specific cost.
- 2026-08-26: Landed direct structural reification. The reconstructor reads the
  nominal `Iff` spine, verifies its two directions, recognizes the two `Le`
  shapes, and preserves neutral `twice` while evaluating only the bounded
  closed carry addend. All eight `carry_threshold` leaves now report direct
  selection and zero candidate probes; reducible aliases retain an explicitly
  measured fallback. Generated and handwritten evaluator metrics remain
  identical with zero eviction. A representative debug profile moved from
  roughly 24 ms total to 11.6 ms (6.0 ms search/elaboration, 5.6 ms final
  gate); handwritten measured 7.9 ms (3.0 ms elaboration, 4.9 ms gate).
  Unsupported leaves include the structured direct-reification reason, the
  majority mutation remains refused, and the focused value-metrics suite is
  green. Merged-tree verification: `scripts/test --fast` reports 1,997 passed,
  zero failed; `scripts/bench --check` reports 106/106 within thresholds.

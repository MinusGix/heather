---
title: "Int I-prime: complete strict order, lattice faces, and nonnegative multiplication monotonicity"
status: closed
labels: [stdlib,proofs,orders]
created: 2026-08-19
updated: 2026-08-19
---

Wave I deliberately cut three coherent pieces from `std/int`: the strict-order
kit beyond its first three facts, carrier-owned `min`/`max`, and multiplication
monotonicity under a nonnegative-factor hypothesis. This is wave I-prime from
[[std-api-waves]], scheduled after [[stdlib-operator-spelling-locality]] made
the public arithmetic and order surface available throughout the file.

## Scope

- Complete the ordinary strict linear-order consequences around `Int::Lt`:
  trichotomy, transitivity, mixed `<=`/`<` transitivity, conversion of a
  non-strict inequality plus disequality to strictness, and the useful negated
  forms.
- Give `Int` carrier-owned `min` and `max` functions backed by its existing
  propositional `le_dec`, together with both bounds, both universal properties,
  and the comparison-selected equations.
- Prove that multiplication by a nonnegative integer preserves `<=`, on both
  sides. The proof should use the existing induction and distributive/order
  kits; it must not reopen the sign representation case-by-case.

`calc` over inequalities remains outside this round. If these proofs produce a
real chain that is materially worse as nested `le_trans`, record that customer
on [[calc-over-order-relations]] rather than adding syntax speculatively.

## Acceptance

- Every new law applies at open integers in `lib_std_int` tests.
- `min` and `max` compute at representative positive, negative, and mixed-sign
  closed inputs.
- Multiplication monotonicity is tested with an open nonnegative multiplier and
  a closed negative multiplier remains excluded by its hypothesis.
- The complete suite passes.

## Log

- 2026-08-19: Scheduled as the next target after the notation-locality round.
  The intended multiplication proof is algebraic: induct over the multiplier,
  eliminate the negative half from `0 <= k`, and use distributivity plus
  two-sided addition monotonicity in the successor step.
- 2026-08-19: Implementation complete pending the full suite. Strict
  trichotomy needs only two representation bridges (negative/nonnegative and
  reversed negative payloads); all derived strict laws are encoding-free.
  `min`/`max` share `le_dec` through `or_pick`, so their ten-law lattice kit is
  branch-local and computes at closed signs. Multiplication monotonicity follows
  the planned `int_ind` proof exactly. None of the proofs produced a relation
  chain large enough to become the first customer for
  [[calc-over-order-relations]].
- 2026-08-19: Closed after the complete suite passed: 1,928 passed, 0 failed.
  Open-law probes cover every new declaration, closed computations cover
  positive, negative, and mixed-sign `min`/`max`, and a negative control proves
  that multiplication monotonicity cannot be invoked at a negative factor.
- 2026-08-19: Post-round surface review produced four owners:
  [[prefix-negation-notation]], [[intro-proof-statement]],
  [[stdlib-surface-style-lint]], and [[decidable-if-expression]]. Two suspected
  gaps were checked and are already supported: the first bridge can be written
  `{ split m; on _ := trivial; }`, and the dependent motive can use
  `n < z -> NegSucc(z) < NegSucc(n)`. These are cleanup/style customers, not
  language blockers.

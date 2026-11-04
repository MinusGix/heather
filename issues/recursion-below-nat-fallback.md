---
title: Lower a refused Nat recursion by below at the top
status: closed
labels: [recursion,elaboration]
area: language
created: 2026-11-03
updated: 2026-11-04
---

Slice 1 of docs/recursion-at-the-top-design.md §4 option A, which Minus
chose 2026-11-04 (issues/recursion-on-elaborated-terms.md).

Where today's planner refuses a structural recursion on `Nat` because of
where the recursion is compiled (the decreasing parameter read inside its
own `match`, directly or through a `let`/`have` above it; a case split whose
ih mentions the split parameter), lower it by `below` at the top instead:

- `Below_M(0) = Unit`, `Below_M(Succ k) = Σ(M(k), Below_M(k))`, one generic
  definition by large elimination into `Type`.
- Motive `M(z) = Π x̄ ȳ. R`, every other parameter generalised.
- `F(z) : Σ(M(z), Below_M(z))` by `elim_Nat`; the whole body is the step,
  elaborated with a map from arm binders (de Bruijn positions) to their
  `below` accessors; a self-call whose decreasing argument elaborates to a
  key is the accessor's `.1`, anything else is refused as not descending.

Nothing accepted today changes its term: the new lowering runs only where
the current one refuses.

## Acceptance

- `lib/_tests/std/core/recursion_at_top_tests.hthr`: the parameter read
  inside its arm (an unused `let`, the arm's value), a `let` above the
  `match` from a varied parameter, an open element type and a `Type`-valued
  recursion, each with `refl` at a literal *and* an open-argument unfolding;
  a negative control refused with the plain lowering's message.
- `heather check --review`'s meaning check passes on them.
- The [[recursion-case-split-dependent-ih]] `walk_shape` example turned out
  not to be a lowering question (docs/recursion-at-the-top-design.md §5),
  so it is not part of this slice.

## Log

- 2026-11-04: 2026-11-04: Built (docs/recursion-at-the-top-design.md §5): a top wrapper over the one-level Nat guard, taking the constructor arm of a Nat match inside it, tried at a ByMeasure plan, a Misplaced refusal and a refused self-call, rolled back on failure. Found and fixed on the way: the planner missed self-calls written inside types, so a Type-valued arm reading its parameter (`n = n ∧ E(k)`) was compiled with the top call's value; it now lowers at the top.
- 2026-11-04: 2026-11-04: Depth *d* at the top (second PR): `cov_depth` is seeded at the parameter in the top wrapper, so the window the body's nested matches convoy reaches calls at any depth (`half_read`, a three-deep `three`, `fib_read` varying a generalized parameter at two depths). Closed; the default flip is [[recursion-at-top-nat-default]].

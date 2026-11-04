---
title: Lower a refused Nat recursion by below at the top
status: open
labels: [recursion,elaboration]
area: language
created: 2026-11-03
updated: 2026-11-03
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

- `lib/_tests/std/core/recursion_binder_tests.hthr`'s `unused_read` and the
  `walk_shape` example of [[recursion-case-split-dependent-ih]] are
  accepted, with `refl` probes at literals *and* a neutral-argument
  unfolding (`f(Succ(k), …) = …` by `refl`), plus a negative control (a
  call on a non-subterm still refused, by name).
- `heather check --review`'s meaning check passes on them.
- Display folds the accessor back to `f(k)` in a goal that whnfs through it.

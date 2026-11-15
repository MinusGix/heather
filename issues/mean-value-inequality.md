---
title: The mean value inequality for the uniform derivative, by telescoping
status: closed
labels: [stdlib,mathematics,constructive]
area: mathematics
milestone: [math-reals, ml-descent]
created: 2026-10-31
updated: 2026-11-01
---

`DerivOn::local_lipschitz` (`lib/std/analysis/real_fn.hthr`) turns a
derivative bounded by `M` into a Lipschitz bound `M + 1` at the scale `δ` of
its modulus. The global statement is the constructive mean value
inequality (docs/library/analysis-foundations-design.md §7.2): if `|g| <= M` on
`[a, b]` and `DerivOn([a, b], f, g)`, then `|f(b) - f(a)| <= M·(b - a)`.

Route:

- At `ε` in place of `1` the local constant is `M + ε`. Cut `[a, b]` into
  `n` pieces no longer than `δ` (Archimedean: `(b - a)/n <= δ`), bound each
  step, and telescope with the range sum
  (`MonoidRel::range`, [[finite-difference-calculus]]'s telescoping lemma).
  That gives `|f(b) - f(a)| <= (M + ε)·(b - a)` for every `ε > 0`.
- Drop the `ε` by the eventual form of `≤` (`le_of_close` at `CReal`; a
  generic `le_of_forall_pos_le` over an ordered field).

Consequences to state with it: `LipschitzOn` from a bounded derivative,
`g ≈ 0` gives `f` constant, and uniqueness of the derivative on an interval
with no isolated points. These are the facts ML descent needs: an
`L`-smooth function's gradient step decreases it.

## Log

- 2026-11-01: Done in lib/std/analysis/real_fn.hthr. `DerivOn::mvi` gives the tight constant M on a convex domain (`ConvexOn`, with `ConvexOn::within` for intervals). The local bound `M + ε` (`local_lipschitz_eps`) is chained in half-modulus steps by induction on the step count (`mvi_steps`), the count comes from `OrderedField::archimedean_mul`, and ε is dropped by `OrderedField::le_of_forall_pos`. No order on the points is decided. Consequences: `DerivOn::lipschitz` (LipschitzOn from a bounded derivative, with `le_by_cases` on the order of the points) and `DerivOn::const_of_zero`. First reals customer: `CReal::exp_lipschitz_within` (lib/std/analysis/real_exp.hthr). The telescoping went by induction, not by the range sum, so it does not depend on [[finite-difference-calculus]]. Uniqueness of the derivative is still open (it needs points that are not isolated) and is logged on [[real-functions-and-derivatives]].

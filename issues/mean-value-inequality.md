---
title: The mean value inequality for the uniform derivative, by telescoping
status: open
labels: [stdlib,mathematics,constructive]
area: mathematics
milestone: [math-reals, ml-descent]
created: 2026-10-31
updated: 2026-10-31
---

`DerivOn::local_lipschitz` (`lib/std/analysis/real_fn.hthr`) turns a
derivative bounded by `M` into a Lipschitz bound `M + 1` at the scale `δ` of
its modulus. The global statement is the constructive mean value
inequality (docs/analysis-foundations-design.md §7.2): if `|g| <= M` on
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

---
title: Dominance relations, convergence, and one Newton lemma
status: open
labels: [stdlib,mathematics,analysis,design]
area: mathematics
milestone: [math-reals]
created: 2026-10-27
updated: 2026-10-27
---

Axis 2 of `docs/analysis-foundations-design.md` (§3.2): smallness as a
dominance relation `≼` with axioms (no totality, leading monomials as data),
convergence for it, and Newton's lemma proved once as a contraction with a
rate.

Scope:

- the dominance interface: preorder, `f ≼ 0 → f ≈ 0`, sums under a common
  bound, multiplicativity, and `≺` with its witness; a witnessed leading
  term where one is needed;
- first round's two instances (§3.7): Landau `O` at an approach (archimedean,
  from [[asymptotic-relations]]) and the `ε`-adic order on series
  (non-archimedean, from [[formal-power-series]]);
- Cauchy convergence for the relation, with rates; `CReal` regularity and
  `ε`-adic stabilisation as instances;
- a fixed-point theorem with rates in a complete structure, and from it
  Hensel's lemma (`v(f(a)) > 2·v(f'(a))`) and Newton–Kantorovich at `CReal`;
- `ℚ_p` as a probe instance only if it costs little.

## What it assumes from elsewhere
- **[[asymptotic-relations]]**: approaches and the Landau closure lemmas.
- **[[formal-power-series]]**: the `ε`-adic instance.

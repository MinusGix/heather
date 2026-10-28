---
title: "Perturbation by Newton's lemma: regular, singular, and width expansions"
status: open
labels: [mathematics,analysis]
area: mathematics
created: 2026-10-27
updated: 2026-10-28
---

Layer F of `docs/analysis-foundations-design.md` (§10): every perturbation
theory here is Newton's lemma in a dominance relation.

Scope:

- regular perturbation: the formal solution of `F(x, ε) = 0` by Hensel
  lifting in the `ε`-adic dominance when `∂F/∂x` is invertible at the base
  point (each coefficient computes at `Rat`), and the order-`N` expansion
  of the true solution with a remainder constant from the archimedean
  Newton lemma;
- instances: a parametrised contraction, and as the first acceptance probe
  the worked example of §10.1: `x² + εx − 1 = 0` near `1`, the truncation
  `1 − ε/2 + ε²/8` by Newton on series in `ε`, its residual `ε⁴/64` by `ring`,
  and the certified expansion with `|R| ≤ C·|ε|⁴` from Kantorovich;
  its being an instance of this issue's theorem closes [[analysis-vertical-slice]];
- singular perturbation of algebraic equations: Puiseux exponents from the
  Newton polygon;
- a width-expansion probe in the shape of Roberts–Yaida–Hanin (a statistic
  of a toy network at order `1/n` with an `O(n⁻²)` remainder over a finite
  dataset);
- a probe reading `Format::gamma` bounds as `n·u + O(u²)` at `u → 0⁺`,
  without restating the float library.

Exponentially small terms and perturbation of differential equations
belong to [[grid-based-transseries]].

## What it assumes from elsewhere
- **[[valued-rings-and-newton]]**: the dominance interface and the Newton lemma.
- **[[formal-power-series]]**: Newton lifting on series.
- **[[certified-expansions]]**: the expansion statement.
- **[[taylor-model-enclosures]]**: bounds uniform in `ε` over `|ε| ≤ r`; the
  general theorem waits for them rather than shipping the polynomial case first.

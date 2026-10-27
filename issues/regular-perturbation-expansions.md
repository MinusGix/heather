---
title: Regular perturbation: formal solutions and their certified remainders
status: open
labels: [mathematics,analysis]
area: mathematics
created: 2026-10-27
updated: 2026-10-27
---

Layer F of `docs/analysis-foundations-design.md` (§9): regular perturbation,
formal by Newton lifting and justified by a contraction with an explicit rate.

Scope:

- formal solution of `F(x, ε) = 0` as a formal power series in `ε` when `∂F/∂x` is invertible at
  the base point; each coefficient computes at `Rat`;
- Banach's fixed-point theorem with rates at `CReal` (if no issue owns it,
  here), giving the order-`N` expansion of the true solution with a
  remainder constant;
- instances: a perturbed polynomial root; a parametrised contraction;
- a probe reading `Format::gamma` bounds as `n·u + O(u²)` at `u → 0⁺`,
  without restating the float library.

Singular perturbation (Puiseux powers, exponentially small terms) is out of
scope and belongs to [[grid-based-transseries]].

## What it assumes from elsewhere
- **[[formal-power-series]]**: Newton lifting.
- **[[certified-expansions]]**: the expansion statement.

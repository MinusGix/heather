---
title: Deliver one certified perturbation expansion end to end before the layers
status: open
labels: [mathematics,analysis]
area: mathematics
milestone: [math-reals]
created: 2026-10-27
updated: 2026-10-27
---

The first round of `docs/analysis-foundations-design.md` (§13, item 0): one
result delivered end to end through every layer, thinly, before the layer
issues are built out horizontally. It tests the architecture (interfaces,
class-system nesting, kernel cost) while it is still cheap to change.

The result is the worked example of §10.1: `x² + εx − 1 = 0` near `x₀ = 1`
has a root `x(ε) = 1 − ε/2 + ε²/8 + R` with `|R| ≤ C·|ε|⁴` for `|ε| ≤ r`,
with `C` and `r` rationals given as data.

Scope, each piece only as large as the result needs:

- **A.** The range sum and the antidiagonal sum, enough for one
  convolution.
- **B.** `Jet(Rat, N)` as a finite vector (the computational form) and
  `Hurwitz<Rat>` with the truncation homomorphism (the reasoning form).
  Newton's step on jets in `ε`.
- **Axis 2.** The dominance relation at its smallest: `≼` on series in `ε`
  and the residual statement `F(x₂, ε) ≈ ε⁴/64`, by `ring`.
- **Newton lemma.** Kantorovich at `Rat`/`CReal`, with explicit constants
  over `|ε| ≤ r`. Bounds uniform in `ε` can come from interval reasoning over
  the range; full Taylor models are not required.
- **D.** The certified-expansion record, instantiated once.
- **Probes on the way.**
  - Is `Hurwitz<Hurwitz<Rat>>` accepted by the class system, so that
    several variables work as iterated series?
  - What is the kernel cost of a coefficient checked by `refl` through jets
    versus through coefficient functions?

Done when the theorem is checked by the whole-library gate. A short note
should also record, for each layer issue, what the slice changed in its
plan: an interface that did not fit, a cost, or a class-system refusal.
Those findings are logged on the owning issues.

## What it assumes from elsewhere
- **[[finite-sums-and-products]]**, **[[formal-power-series]]**,
  **[[valued-rings-and-newton]]**, **[[certified-expansions]]** and
  **[[regular-perturbation-expansions]]** own their layers. The slice
  builds the minimum of each in their files and leaves their scope to them.
- **[[ring-modulo-a-relation]]**: `ring` at `≈`.

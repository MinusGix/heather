---
title: Design a constructive ordered-field interface
status: open
labels: [stdlib,mathematics,reals,algebra,order]
created: 2026-09-02
updated: 2026-10-16
---

Identify the abstract ordered-field structure actually shared by rationals and
constructive real presentations. Treat setoid equality, strict order,
non-strict order, apartness, positivity, inverse-on-apart elements, and the
Archimedean property explicitly; do not smuggle classical trichotomy or
decidable equality into the name.

Probe whether locatedness belongs in the base interface or in a separate
capability. The acceptance should state useful generic interval/absolute-value
theorems at the weakest demonstrated layers.

## What it assumes from elsewhere

- **[[ordered-algebra-api]]** owns order/algebra compatibility.
- **[[apartness-structures]]** owns apartness laws.
- **[[positive-naturals-and-rationals]]** supplies the first carrier.

## Log

- 2026-09-02: Filed to provide shared real-number mathematics without claiming
  that every presentation is definitionally or constructively identical.
- 2026-10-14: `Rat` has the pieces an instance would fill ([[rational-order-completion]], docs/rational-order-round.md): `≈`, `≤`, positive-difference `<` with cotransitivity and tightness, `abs`, inverse on `¬(x ≈ 0)`, and both Archimedean forms. Note: `Rat` can't instantiate `PartialOrder` because `Antisymmetric` is stated with `=`; the interface needs antisymmetry modulo its setoid.
- 2026-10-16: `CReal` is the second carrier (docs/regular-cauchy-reals-round.md, "What the ordered-field interface learns"). Nothing decides there: no `le_dec`, no decidable `≈`, no trichotomy. Both carriers share `≈` as an `Equivalence`, a `<` that is irreflexive, transitive, respects `≈` and is cotransitive, and tightness as "not apart gives `≈`". `<` is data at both, so the interface should take `<` as primitive and `≤` as `¬(y < x)`. Cotransitivity at `CReal` is locatedness and costs nothing, which argues for locatedness in the base interface for Cauchy-style carriers.

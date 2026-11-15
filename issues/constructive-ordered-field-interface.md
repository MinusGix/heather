---
title: Design a constructive ordered-field interface
status: closed
labels: [stdlib,mathematics,reals,algebra,order]
created: 2026-09-02
updated: 2026-10-19
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
- 2026-10-14: `Rat` has the pieces an instance would fill ([[rational-order-completion]], docs/library/rational-order-round.md): `≈`, `≤`, positive-difference `<` with cotransitivity and tightness, `abs`, inverse on `¬(x ≈ 0)`, and both Archimedean forms. Note: `Rat` can't instantiate `PartialOrder` because `Antisymmetric` is stated with `=`; the interface needs antisymmetry modulo its setoid.
- 2026-10-16: `CReal` is the second carrier (docs/library/regular-cauchy-reals-round.md, "What the ordered-field interface learns"). Nothing decides there: no `le_dec`, no decidable `≈`, no trichotomy. Both carriers share `≈` as an `Equivalence`, a `<` that is irreflexive, transitive, respects `≈` and is cotransitive, and tightness as "not apart gives `≈`". `<` is data at both, so the interface should take `<` as primitive and `≤` as `¬(y < x)`. Cotransitivity at `CReal` is locatedness and costs nothing, which argues for locatedness in the base interface for Cauchy-style carriers.
- 2026-10-18: - 2026-10-18: `Rat`'s inverse now takes `x.Apart(0)` (searched, `x⁻¹`), the total reciprocal is `Rat::recip`, and both carriers have `x ^ n` with `x ^ (-1) ≈ x⁻¹` ([[inverse-power-notation]], docs/library/inverse-power-notation-design.md). An interface can take `inv` at apartness and `pow` at `PowOk` uniformly.
- 2026-10-19: Landed (docs/library/constructive-ordered-field-design.md). `lib/std/algebra/ordered_field.hthr` has five layers, indexed by `≈`, `<`, `≤`, `+`, `*`: `StrictOrder` (setoid, tight strict order, `≤` ⇔ `¬>`), the `Cotransitive` capability and `PseudoOrder`, `OrderedAddGroup`, `LocatedAddGroup`, and `OrderedField` (inverse at `ApartBy(<, x, 0)`, `mul_pos`, `0 < 1`, Archimedean over an `of_nat` field). `Rat` and `CReal` fill every layer; `CReal` gained `archimedean`. Answer to the locatedness probe: it is a separate capability, since `StrictOrder` alone gives open intervals, apartness, `≤` antisymmetry and the bounded triangle inequality, while `≤` transitivity, closed intervals and a bound's positivity need it (refusal controls in crates/elab/tests/lib_std_ordered_field.rs); both carriers here have it. Absolute value is stated as bounds (`AbsLt`, `AbsLe`, `Close`), so `CReal` needs no `abs`. Residue: the inverse's sign and the `inv_succ` Archimedean form need multiplication to reflect positivity ([[ordered-field-inverse-sign]]); index pinning against unfolded expected types ([[constrained-predicate-expected-type]]); `pow` stays with [[inverse-power-notation]].

---
title: linarith at ordered fields, up to the field's setoid equality
status: closed
labels: [tactics,arith,reals]
area: tactics
milestone: [tac-arith]
created: 2026-10-27
updated: 2026-10-28
---

omega proves linear facts over `Int` and `Nat`, and over `Rat` only when the
rationals' structure is concrete (`Rat::ofInt(OfNat(m)) * Rat::inv_succ(k)`).
Over abstract rationals it unfolds `≈` and `<=` to cross products of numerators
and denominators, which are nonlinear, and the real shadow finds no
contradiction. So a linear rearrangement such as `(b + u) - c ≈ (b - c) + u`,
or `a <= q + (e + r)` with `e <= f` giving `a <= (q + r) + f`, is written as a
calc chain of `add_assoc` / `add_comm` / `add_le_mono`, or as a one-off lemma
in `rat.hthr` (`Rat::le_add_shift`, `Rat::sub_le_shift`, `Rat::neg_gap` exist
only for this). `lib/std/num/float/series.hthr` and `creal_interval.hthr`
carry dozens of such steps.

Wanted: `linarith`, Fourier–Motzkin (or simplex) over an ordered field, read at
the field's setoid equality, so that it closes the same goals at `Rat` and at
`CReal`.

Scope:

- atoms are the maximal non-linear subterms (products of two atoms, function
  applications), and coefficients are rational numerals;
- hypotheses are `<`, `<=` and `≈` facts passed as arguments (`linarith(h1,
  h2)`, as `omega(h, …)` takes them) plus the goal's negation;
- the certificate is a nonnegative combination of the hypotheses, and it is
  checked through the `OrderedField` laws (`add_le_mono`, scaling by a positive
  numeral, `le_respects` for `≈`). So it works at any instance, not only by
  unfolding `Rat`;
- at `CReal`, `<=` is a refutation, so the check needs the instance laws only.
  It never decides an order.

`ring-inequalities` is the Int-atom route, where `ring` normalises and omega
compares. This issue is the field-generic one, and the two should share the
normaliser.

## What it assumes from elsewhere
- **[[ring-inequalities]]**: the polynomial normaliser.
- **[[ordered-algebra-api]]**: the class laws a certificate is checked against.

## Log

- 2026-10-27: [[field-simp]] closed for equations: `ring` at a field clears
  denominators itself (docs/tactics/ring-normalization-design.md §9), the
  reciprocals' multipliers computed by elimination. The inequality form it
  left (positive denominators preserve `<=`, so `a * d⁻¹ <= b` becomes
  `a <= b * d` given `0 < d`) belongs here: the cleared polynomial and the
  denominator product are what `clear_denominators` already returns.
- 2026-10-27: Built (docs/tactics/linarith-design.md). `linarith` / `linarith(h, …)` proves `<`, `<=`, `≈` and `¬(a < b)` at a carrier with the new `OrderedFieldOfInt` (`OrderedField` + `CommRingOfInt`; Rat and CReal), and any goal from contradictory facts; written facts first, then the context's. Fourier–Motzkin over `ring`'s reader (`ring::FieldReading`, one atom table); the certificate is the direct form `k·(b − a) ≈ Σ λᵢ·(hiᵢ − loᵢ) + c`, its parts and sums from lib/std/tactic/linarith.hthr's generic lemmas and the identity by `ring`, so no order is decided and `a < b` is provable at CReal. `Rat::neg_gap`, `le_add_shift`, `sub_le_shift` are one call each; two of series.hthr's shift chains too. `ring` now names atoms it cannot spell by alias (closes [[ring-field-read-atom-spelling]]). The denominator form is filed as [[linarith-positive-denominators]].
- 2026-10-28: [[ring-inequalities]]'s Int-atom route landed as `linarith` at `Int`/`Nat` over the same reader (`FieldReading::integral`), design §8.

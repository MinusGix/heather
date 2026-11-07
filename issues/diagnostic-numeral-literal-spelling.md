---
title: Spell Int and Rat numerals as numerals in diagnostics
status: closed
labels: [frontend,diagnostics,notation,ergonomics]
area: language
created: 2026-11-06
updated: 2026-11-07
---

A diagnostic spells a Nat numeral as the numeral (`3`, not `S(S(S(0)))`),
but an `Int` or `Rat` numeral as the constructor calls it elaborated to:
`x ^ OfNat(2)` for `x ^ 2` at `Rat` (the exponent is an `Int`), and
`ofInt(OfNat(0))` for `0` at `Rat`:

```
no instance for `Apart(b * b, ofInt(OfNat(0)))`
```

Since [[diagnostic-operator-resugaring]] the operators around them read as
written, which leaves these as the conspicuous remainder.

Wanted: the speller recognises a numeral's elaborated form at each carrier
that has numerals (`OfNat(k)` and `NegSucc(k)` at `Int`, `ofInt(…)` at
`Rat`, and whatever the carrier-directed numeral route emits elsewhere,
docs/carrier-directed-numerals-design.md) and prints the numeral, `-k` for a
negative one (`operand_at` already parenthesizes a spelling that starts with
`-` as a prefix form). The inverse must be exact in the same sense as the
operator one: print the numeral only where the numeral written at that
carrier would elaborate to this term, and never reduce to find out.

## Acceptance

- `lib/_tests/std/num/operator_display_tests.hthr` gains probes showing
  `x ^ 2` at `Rat` and `Apart(b * b, 0)`.
- A literal whose carrier has no numeral route keeps its constructor
  spelling.

## Log

- 2026-11-07: Done. The speller reads the `Numeral` instance table backwards
  (`Speller::carrier_numeral`, docs/surface-type-display-design.md §5.3): each
  closed instance's `ofNat` body is a template over the literal, read off the
  dictionary's definition without reducing anything, and a term spells as the
  numeral `k` exactly when it is that template at `k` in its own scope. Int,
  Rat, Dyadic and CReal numerals now read as written (`x ^ 2`, `Apart(b * b,
  0)`, `-3` as the negation of `3`). Deliberately not spelled as numerals:
  `NegSucc(k)`, which a written `-(k + 1)` does not elaborate to (it
  elaborates to `Int::neg(OfNat(k + 1))`), so showing it as `-(k + 1)` would
  print a reduct as its redex; and the numerals of parameterized instances
  (`BitVec(n)`, `SInt(n)`), which still show `ofNat(3)` because their template
  has the instance's parameter in it as well as the literal.

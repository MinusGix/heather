---
title: Spell Int and Rat numerals as numerals in diagnostics
status: open
labels: [frontend,diagnostics,notation,ergonomics]
area: language
created: 2026-11-06
updated: 2026-11-06
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

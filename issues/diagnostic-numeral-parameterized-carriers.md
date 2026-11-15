---
title: Spell numerals at parameterized carriers (BitVec(n), SInt(n)) as numerals in diagnostics
status: open
labels: [frontend,diagnostics,notation,ergonomics]
area: language
created: 2026-11-07
updated: 2026-11-07
---

Since [[diagnostic-numeral-literal-spelling]] a diagnostic spells a numeral at
`Int`, `Rat`, `Dyadic` or `CReal` as the numeral, by reading each closed
`Numeral` instance's `ofNat` body backwards (`Speller::carrier_numeral`,
docs/elaborator/surface-type-display-design.md §5.3). A parameterized instance
contributes no template, so `3` at `BitVec(8)` still reads `ofNat(3)`, and
the same at `SInt(n)`.

Wanted: a parameterized instance's template, with the instance's parameters
as holes beside the literal's. The matcher already finds the literal as the
template's first difference from the term; with several holes it can bind
them one difference at a time (each hole a distinct marker variable) and then
compare the whole. The instance's parameters are bound in its binding's
context rather than by a λ, so the template has to be read under that
context.

## Acceptance

- `lib/_tests/std/num/operator_display_tests.hthr` (or a bitvec probe file)
  shows `x = 3` for a numeral at `BitVec(8)`.
- `BitVec::ofNat(k)` at a `k` that is not a literal keeps its call spelling.

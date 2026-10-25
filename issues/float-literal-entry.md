---
title: Float and decimal literals, with a printer whose round trip is proved
status: open
labels: [language,syntax,floating-point]
area: language
created: 2026-10-25
updated: 2026-10-25
---

Heather has no float literal and no decimal-fraction literal. Numerals are
the only `Rat`/`CReal` constants, and `docs/radix-numerals-design.md` covers
only integers. Tests and clients build floats from fields. The Coq
hardware-float survey (`docs/coq-hardware-floats-survey.md` §5.3) sets out
the design Coq landed on, and the part Coq could not do that Heather can.

## Proposal

- **Exact hexadecimal float spelling** (`0x1.8p3`, `-0x1p-149`), extending
  the radix-numeral grammar. It denotes a `Dyadic`, and at a `Float(F)`
  expected type it is accepted only when representable. It is the
  information-preserving raw printing form.
- **Decimal spelling that rounds** (`0.1`, `1e-3`): it denotes the `Rat`,
  and at a `Float(F)` expected type it elaborates to `Format::round_rat`
  under `NearestEven`, the format taken from the expected type as for
  carrier-directed numerals. A warning appears when the value is inexact,
  decided by `round_rat_exact`.
- **A printer with a proved round trip.** Coq prints with `printf "%.17g"`
  and leaves an in-language printer as future work. Heather's printers are
  in-language already (`docs/parser-canonical-printers-design.md`), so
  the paper's Lemma 1 can be a theorem: for a format of precision `p`
  and output radix `β'` with `2^p < β'^(p'-1)`, printing `p'` significant
  digits and parsing by nearest rounding gives back the same float. Nine
  digits for binary32 and seventeen for binary64 are corollaries, and the
  shortest round-tripping output is a refinement.

Decimal literals at `Rat` (`0.5 : Rat`) fall out of the same grammar.
[[rat-numerals-and-semigroup-clash]] and [[all-numeral-relations-default-to-nat]]
show what defaulting such a literal must avoid.

## Done when

The lexer accepts both spellings, both elaborate at `Float(F)` and `Rat`,
the inexact warning fires and has a test, and the round-trip theorem is
proved for every `Format` (in `lib/std/num/float/`) for the printer that
renders floats.

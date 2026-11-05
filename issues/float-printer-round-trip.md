---
title: Float printer with a proved round trip
status: open
labels: [floating-point,syntax]
area: language
created: 2026-10-26
updated: 2026-10-26
---

Split from [[float-literal-entry]], which landed the parsing half: decimal
and hex literals elaborate at every `Float(F)` through
`Format::round_decimal`, proved a correct rounding
(`lib/std/num/float/literal.hthr`, `docs/floating-point-design.md` §15).

What remains is the printing half. Heather's printers are in-language
(`docs/parser-canonical-printers-design.md`), so the Coq survey's Lemma 1
(`docs/coq-hardware-floats-survey.md` §5.3) can be a theorem: for a format
of precision `p` and output radix `β'` with `2^p < β'^(p'-1)`, printing `p'`
significant digits and reading the result back with `round_decimal` under
`NearestEven` gives the same float. Nine digits for binary32 and seventeen
for binary64 are corollaries; the shortest round-tripping output
(Ryū / Grisu style) is a refinement, not the first step.

## Proposal

- A digit generator `Float::digits(x, p') → Decimal` (exact division by a
  power of ten, rounded to `p'` digits) and a `Show`-style renderer.
- Lemma 1 against `round_decimal_correct`: the printed decimal lies within
  half an ulp of `x`, so its nearest rounding is `x`. The window machinery
  keeps the evaluation at `prec + c` bits for the same reason it does for
  literals.
- The hex printer is exact and needs no theorem beyond `hex_exact`.

## Done when

`Float::digits` and the renderer exist, Lemma 1 is proved for every `Format`
in `lib/std/num/float/`, and the 9/17-digit corollaries are stated.

## Log

- 2026-11-05: gardener: cites a file it shares with [[parser-canonical-printers]] (`docs/parser-canonical-printers-design.md`).

---
title: Numerals of any size
status: closed
labels: [language,kernel,syntax]
created: 2026-09-26
updated: 2026-09-26
---

A numeral was a `u64` from the lexer to the kernel, so `18446744073709551616`
(2^64, the first number a 64-bit word cannot hold) did not lex. Mathematics
needs such numbers constantly — a word's bound is one — and the workarounds
were `Nat::pow(2, 64)` or `omega`'s byte chain `add(mul(x, 256), b)`.
Numerals are now arbitrary-precision everywhere: `docs/language/wide-numerals-design.md`.

Raised by [[bv-omega-check-cost]]'s attempt to present a word's bound as the
number it is.

## Acceptance

- A numeral of any size lexes in all four radixes, elaborates at `Nat`, and
  is the number it spells to evaluation and conversion; neighbours differ.
- Positions that need a machine integer refuse a larger numeral with a reason.
- `omega` spells and reads its constants as numerals.
- Module images and the cache round-trip wide literals; a small literal hashes
  as it always did.

## Log

- 2026-09-26: LANDED. `heather-numeral` (new crate, first-party, no dependencies) holds `Numeral`; the lexer reads any digit string in all four radixes, `ExprKind::Num`/`TokKind::Num` and `Term::NatLit` carry it, evaluation builds a wide literal as a shared run program from its bits, module images (format bumped to 09/08) and the cache hash it (a small literal keeps its old hash), display and `omega`'s speller print it, and `omega` spells its constants as numerals (the byte chain is gone). Machine-integer positions (universe levels, `inj`'s field index, `Fin` indices, word widths, tag and certgen readers) take `as_u64()` and refuse or decline above it. Tests: the numeral crate's own, the lexer in every radix, the kernel's evaluation of wide literals to their exact counts, and `large_nat_literals::numerals_past_a_machine_word_are_the_numbers_they_spell` with three negative controls. Full suite green (3,008 passed); `scripts/bench --check` shows only the pre-existing `wf/check-tree` slope band.

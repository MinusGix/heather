---
title: Char and String as specification types, with literals
status: open
labels: [stdlib,frontend,syntax,elaboration,design]
created: 2026-09-18
updated: 2026-09-18
---

`Char` and `String` as specification types, with literals. Design record:
`docs/string-char-design.md` (2026-09-18).

Decisions: `Char` is a Unicode scalar value (below `0x110000`, no
surrogates) as a record over `Nat` with a truncated `scalar` witness;
`String` is a one-field record over `List<Char>`; UTF-8 is a *repr* of
`String` under [[datarepr-separation]], not its definition, and no
`Utf8String`/`Utf32String` spec types exist. Byte-level meaning gets a
separate `Utf8` spec type with the encode/decode iso in a later round.

## Plan

- Round 1 (this issue): `lib/std/char.hthr`, `lib/std/string.hthr`; `'x'`
  and `"…"` literals in the lexer, parser and elaborator, with `CharLiteral`
  and `StringLiteral` classes beside `Numeral` for other carriers; tests per
  the design doc §4.
- Round 2: `encode`/`decode`, the round-trip theorem, `utf8_valid`, and the
  `Utf8` record; see the design doc §5.
- Later, behind a consumer: a `Char`-token lexer for the parser library,
  char classes, and the UTF-8 runtime repr once
  [[byte-memory-access-model]] exists.

## Log

- 2026-09-18: Round 1 landed: `lib/std/char.hthr`, `lib/std/string.hthr`, the two lexer
  tokens with their parser and elaborator forms, and the `CharLiteral` /
  `StringLiteral` classes (in `char`/`string` rather than `algebra`, which
  would have had to import them). Filed on the way:
  [[le-lt-conversion-linear-in-literal]], which refused the first spelling of
  `scalar_dec`.

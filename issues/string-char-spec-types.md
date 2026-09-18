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
- 2026-09-18: Follow-ups filed from review 2026-09-18: [[derive-decide-instances]] (no hand-written `scalar_dec`), [[member-shadows-receiver-member]] (the `string_len` delegation), [[derive-record-injectivity-congruence]] (`code_injective`, `chars_injective`). Library rework in flight: `chars_nth` and the `List<Char>` helpers go; list equality becomes generic in `list`.
- 2026-09-18: Rework landed. `logic::DecEq<A>` is the carrier-level equality
  class (instances at `Nat`, `Char`, and `List<A>` given `DecEq<A>`);
  `list::list_eq_dec` is the generic decider and `list` now owns
  `is_nil`/`head_or`/`nil_ne_cons`/`cons_ne_nil`/`cong_head`/`cong_tail`/`cons_eq`
  at an open element type. `string.hthr` keeps no `List<Char>` helper at all:
  `String::nth` recurses on the `String` under a `decreases` measure and
  `string_eq_dec` calls the generic decider. Filed on the way:
  [[instance-binder-occurrence-through-binder-types]], which refused the
  value-generic `Decide<xs = ys>` bridge, and
  [[generic-congruence-inferred-type-arg-level-mismatch]], which forced
  `cong_tail<A>(p)` at one use site.
- 2026-09-18: Round 2 chartered 2026-09-18: docs/string-char-design.md §5. Finding on the way: a truncated `Char.valid` cannot refute a decoder (squash eliminates only into squash), so the witness becomes Bool-reflected (`IsTrue(is_scalar(code))`), which also makes `Decide<scalar(code)>` a one-line match.
- 2026-09-18: Round 2 landed, theorems 1–6. `lib/std/utf8.hthr` — `encode`/`decode`
  with Rust's strict `from_utf8` rejections, the `Utf8` record, `ofString` and
  `Utf8::toString`; `lib/std/char.hthr`'s witness is now `IsTrue(is_scalar(code))`
  and `scalar_dec` is gone. Kit that had to be built on the way, each where the
  fact belongs: `bool`'s `IsTrue` section, `nat`'s `leb`/`Le` bridge and
  `half_lt_of_lt_double`, `bitvec`'s `toNat_ofNat` (theorem 1, which `bitvec`
  did not have), `option::some_inj`. Theorem 7 (`encode_decode`) did **not**
  close: it needs to invert `decode_at` at an abstract lead byte, and the byte's
  class is computed inside the decoder's body rather than passed to it, so there
  is no motive to case on — `docs/string-char-design.md` §5.5 records the way
  through. Filed on the way: [[utf8-decode-conversion-blowup]], which forced
  `push_step` to be stated at `emit` rather than at `decode_char`.
- 2026-09-18: Round 2 landed 2026-09-18: `lib/std/utf8.hthr` with theorems 1–6; the strictness theorem is [[utf8-encode-decode-strictness]]; the fuel-shaped decoder is [[list-course-of-values-recursion]]; conversion finding [[utf8-decode-conversion-blowup]].
- 2026-09-18: Theorem 7 closed 2026-09-18 ([[utf8-encode-decode-strictness]]), and theorem 8 with it: `Utf8` and `String` are mutually inverse presentations. docs/string-char-design.md §5.6.

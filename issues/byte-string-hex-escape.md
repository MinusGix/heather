---
title: A byte string cannot spell a byte above 0x7F (`\xHH`)
status: open
labels: [surface-syntax,literals,lexer]
area: language
created: 2026-11-16
updated: 2026-11-16
---

`b"…"` (docs/native/io-programs-design.md §5 D3) is read by the parser as
the name `b` with a string literal right after it
(`Parser::byte_string`), so its bytes are the string's characters, and it
refuses any character that is not ASCII: a byte string never means more
bytes than it shows characters. A byte from `0x80` to `0xFF` therefore has
no spelling inside one; today it is a numeral in a vector literal
(`[0xC3, 0xA9]`).

Wanted: `\xHH`, as Rust has it: any byte in a byte string, and in a string
or character literal only `\x00`–`\x7F` (so a string stays a sequence of
scalar values). That is a lexer change, and the lexer is held to Heather's
own scanner (`lib/lang/lexer/lexer_scan.hthr`, `crates/linked/CLAUDE.md`):
the escape states of the automaton, a refusal reason for a high `\x` in a
string, `scripts/linked` and `scripts/lexer-probes`. Two ways to carry the
byte to the parser:

- a `ByteStr` token kind (`b"` opens it), so the lexer decides the bytes
  and the parser stops reading adjacency; one more row of `TOKEN_KINDS`;
- or keep `b` + string and have `Str` carry raw bytes, which every other
  reader of `Str` would then have to decode.

The first is the honest one; the parser's adjacency rule was chosen only
because it needed no scanner change.

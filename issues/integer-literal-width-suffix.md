---
title: Integer literals with a width suffix: 42u64, 0x80u8
status: closed
labels: [frontend,syntax,numerals,ergonomics]
area: language
created: 2026-11-12
updated: 2026-11-12
---

A numeral takes its type from where it stands: `i + 1` at `i: u64` is `BitVec::ofNat(1)` already (with `import algebra`), and that holds inside a `runtime fn`. Where nothing gives the type, the only spellings are `BitVec::ofNat(42)` under an annotation or `(42: u64)`. Minus's proposal (2026-11-12): a suffix as in Rust, `42u64`, `0x80u8`, `7i32`.

- `42u64` is `(42: u64)`: the suffix is a width-family name ([[fixed-width-integer-types]]), so any `u<n>`/`i<n>` works and nothing is a keyword.
- A bare `42u` ("a word of whatever width is wanted") adds little: where the width is known a plain `42` already means that, and where it is not known `42u` has nothing to solve it from. It would only say "not a `Nat`" to the all-numeral default ([[all-numeral-relations-default-to-nat]]); to decide.
- Lexing: `42u64` must become one token (or a numeral directly followed by an identifier with no space, read by the parser), in the Rust lexer, tree-sitter and `lib/lang/lexer`. Hex needs care: `0x1f` followed by `u8` is unambiguous, but `0xau8` reads oddly and `0x1fi8`'s `f` is a digit; Rust allows `_` before the suffix (`0x1f_u8`).
- Display: a diagnostic that prints a literal at a word type could use the suffix ([[diagnostic-numeral-parameterized-carriers]]).

Done when: `let mut i = 0u64;` elaborates, the three lexers agree on it, and the formatter keeps it.

## Log

- 2026-11-12: Decided by Minus (2026-11-12): `42u64` goes ahead; no bare `42u`.
- 2026-11-12: Built by PR #585 (merged): `42u64`, `0x80u8`, `7i32` lex as `SuffixedNum` (the scanner's `Num`), with no context dependence. `42u` with the width inferred was considered and skipped (Minus, 2026-11-12): a numeral already takes its width from where it stands.

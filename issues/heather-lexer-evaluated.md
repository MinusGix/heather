---
title: Heather's lexer as a pure Heather function, checked against the Rust lexer line by line
status: open
labels: [self-hosting,lexer]
area: heather-in-heather
milestone: [self-lexer]
created: 2026-11-07
updated: 2026-11-10
---

The first slice of [[self-hosted-lexer]] that can start on master today:
Heather's lexer as an ordinary Heather function evaluated by the kernel,
checked against `crates/syntax/src/lexer.rs` line by line, with no native
compilation. Its done-when is not the milestone's (that needs `heather-lex`
compiled natively); it is the reference the native lexer is later proved
against.

## Why this slice, and why now

The readiness assessment of 2026-11-07 (logged in [[self-hosted-lexer]])
found the language and library ready for a pure lexer, and the native path
not ready. A probe (`self-lexer/lex_probe.hthr` in the project folder): a
byte-at-a-time state machine for identifiers, decimal numerals, eight
punctuation marks, `->`, whitespace and `//` comments, written with `for`,
`let mut` and statement `match` over `List<BitVec(8)>`, checked by `refl`
against literal sources at the first attempt. At 1 KB of real `lib/` text it
cost about 400 kernel steps per byte.

## Scope

- `lib/lang/lexer.hthr` (or wherever `lib-layout` puts it): `Tok`, `TokKind`
  and `LexError` mirroring the Rust types, with spans as byte offsets, and
  `lex(bytes: List<BitVec(8)>) → Result<List<Tok>, LexError>`. Numerals hold
  their value as `Nat` (and scaled literals their parts); identifiers,
  strings and characters hold their bytes or `Char`s.
- The step is a state machine over bytes, one byte at a time, with the
  bounded lookahead the Rust lexer uses (`::` before an identifier start,
  `//`, the two-, three- and five-byte Unicode windows, a numeral's fraction
  and exponent) held in its state. That is the shape a streaming `runtime fn`
  needs later, so the native round reuses the step rather than rewriting it.
  Worth weighing: the step as a table-driven DFA generated from token
  regexes, which is [[regex-dfa-compiler]]'s customer too.
- Theorems in the module: the lexer is line-local (lexing `a ++ "\n" ++ b`
  is lexing `a` and `b`, the second's spans shifted), since a literal cannot
  span lines and comments end at the newline; spans are increasing and
  inside the input; an identifier token is maximal.
- A differential gate: for each line of each file under `lib/`, a theorem
  `lex(<line>) = <tokens the Rust lexer gives>` by `refl`, written by a Rust
  test from `heather_syntax::lex`. Line-locality is what makes per-line
  theorems exact, and it keeps every literal under the stack ceiling
  ([[long-string-literal-stack-overflow]]) and the per-declaration fuel. The
  whole library is about 130k lines and 7 MB, so the gate samples files (or
  runs nightly) rather than checking every line on every run.

## Done when

`lex` mirrors the Rust lexer's token set and errors; the line-locality
theorem is proved; the differential test passes on a sample of `lib/` that
covers every `TokKind`, with a negative control (a perturbed expected token
refused).

## What it assumes from elsewhere

- **[[self-hosted-lexer]]** owns the native `heather-lex` and its done-when.
  Assumed here: only that a pure lexer with this step shape is what it
  compiles.

## Log

- 2026-11-10: `docs/native-lexer-crypto-roadmap.md` §3 splits the lexer in two: a
  **scanner** (kinds and spans over bytes, state held in words) and
  **values** (numeral and string payloads, built from a span on demand). The
  scanner is the half that is compiled and linked ([[self-lexer-linked]]); the
  values stay evaluated first. Write this slice with that seam: the agreement
  theorem against the Rust lexer is then stated once for the scanner and
  reused by the linked export, and nothing in the scanner's state needs a heap.

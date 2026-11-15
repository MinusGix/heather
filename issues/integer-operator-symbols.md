---
title: Operator symbols for division, remainder, shifts and bitwise words
status: closed
labels: [surface-syntax,stdlib]
area: heather-in-heather
created: 2026-11-03
updated: 2026-11-06
---

`/`, `%`, `<<`, `>>`, `&` and `|` do not lex today (`crates/syntax/src/lexer.rs`:
`&` and `|` alone are errors outside `⟨…⟩`, and `//` is a comment), so on
`u8`/`i8` division, remainder, shifts and the bitwise operations are methods:
`a.udiv(b)`, `x.div(y)`, `x.shift_right(2)`, `a.band(b)`
(docs/library/fixed-width-integers-design.md §6).

Wanted: the symbols as designation slots, so `designation / at SInt(n) :=
SInt::div` makes `a / b` read as Rust's at `i64` and `designation >> at
SInt(n)` is the arithmetic shift. Questions: `/` beside `//` comments; `&`/`|`
beside `&&`/`||` and the `⟨a |⟩` injection; whether `/` at `Nat`/`Int`/`Rat`
gets a designation in the same round (`Rat` has `⁻¹`, `Nat::div` exists); and
the tree-sitter inventory (new lexer symbols must be added there).

## Log

- 2026-11-05: gardener: cites a file it shares with [[notation-extensibility]] (`crates/syntax/src/lexer.rs`); [[self-hosted-lexer]] (`crates/syntax/src/lexer.rs`).
- 2026-11-06: Done. `/ % << >> & |` lex (`Slash`, `Percent`, `Shl`, `Shr`, `Amp`, `Pipe`) and are designation slots: `designation / at …`, `Monoid(>>)`, `op as |`. Answers to the questions: `//` stays a comment, so `a // b` is `a` as in Rust; `&&`/`||` are matched first, and a `|` directly before `⟩` is the left injection, so `⟨a | b |⟩` injects `a | b` (the bare-`|` lex error is gone); `>>` lexes as a shift only after a space, `(` or `,`, so `List<List<A>>` is two closers as before and `a>>b` is refused with a message naming `a >> b`. Rust's rungs between `&&` and `+`; `/` `%` beside `*`. Designations: `BitVec(n)` (`udiv`, `urem`, `band`, `bor`, `shift_left`, zero-filling `shift_right`), `SInt(n)` (truncating `div`/`rem`, arithmetic `>>`), `Nat` and `Int` (`div`/`mod`, Euclidean at `Int`). A shift's count is a `Nat` and the carrier probes skip it. `Rat`'s `/` is a decision of its own: [[rat-division-symbol]]. Xor has no symbol (`^` is power). The tree-sitter grammar has the symbols (an external scanner, `src/scanner.c`, sees the space before `>>`), the inventory and both `highlights.scm`, and `src/parser.c` is regenerated. docs/library/fixed-width-integers-design.md §4.1.

---
title: Operator symbols for division, remainder, shifts and bitwise words
status: open
labels: [surface-syntax,stdlib]
area: heather-in-heather
created: 2026-11-03
updated: 2026-11-03
---

`/`, `%`, `<<`, `>>`, `&` and `|` do not lex today (`crates/syntax/src/lexer.rs`:
`&` and `|` alone are errors outside `⟨…⟩`, and `//` is a comment), so on
`u8`/`i8` division, remainder, shifts and the bitwise operations are methods:
`a.udiv(b)`, `x.div(y)`, `x.shift_right(2)`, `a.band(b)`
(docs/fixed-width-integers-design.md §6).

Wanted: the symbols as designation slots, so `designation / at SInt(n) :=
SInt::div` makes `a / b` read as Rust's at `i64` and `designation >> at
SInt(n)` is the arithmetic shift. Questions: `/` beside `//` comments; `&`/`|`
beside `&&`/`||` and the `⟨a |⟩` injection; whether `/` at `Nat`/`Int`/`Rat`
gets a designation in the same round (`Rat` has `⁻¹`, `Nat::div` exists); and
the tree-sitter inventory (new lexer symbols must be added there).

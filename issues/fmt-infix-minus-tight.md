---
title: The formatter writes infix subtraction tight, as `d -8`
status: closed
labels: [tooling,syntax]
area: language
created: 2026-10-21
updated: 2026-10-21
---

`crates/syntax/src/fmt.rs` treats every `Minus` token as a prefix operator
(`if matches!(a.kind, Neg | Minus | Bang | Dollar) && !declared(a)`), so it
hugs the next token. That was right when [[heather-formatter]] landed,
because `-` was prefix-only. Infix subtraction has since landed
([[infix-subtraction-notation]]), and the gate now rewrites `d - 8` to
`d -8` and `i - 64` to `i -64`. The library holds about 400 such
spellings (`address -io_page_base()`, `(0x400000 + k) -0x400000`), against
about a dozen spaced ones the formatter has not reached.

The fix is the role table [[heather-formatter]] planned for exactly this
case: classify `-` as infix where the AST has it between two operands, and
as a prefix only where it opens an operand. The reformat that follows is
whitespace only and reviewable in bulk, as the first one was.

Found when `scripts/test`'s format gate rewrote
`lib/native/function_ir/function_ir_lower_calls.hthr` (S4 round 3,
[[function-ir-verified-lowering]]).

## Log

- 2026-10-21: Closing. `crates/syntax/src/roles.rs` records a `TokenRole::InfixMinus` for the operator of every parsed `l - r` (the first `-` between the two operands' spans; the head's own span is the whole application), and `fmt.rs` spaces that `-` like `+` and keeps every other `-` a tight prefix. A file that does not parse now keeps every `-` gap as written, as it already did for `<`; "parsed" is no longer read off a non-empty role map (a parsed file with no argument lists used to read as unparsed; no library file depended on that). The library was then reformatted with `scripts/fmt` alone, whitespace only (`git diff -w` empty).

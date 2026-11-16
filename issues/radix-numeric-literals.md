---
title: Add radix-aware numeric literals
status: closed
labels: [frontend,syntax,ergonomics]
created: 2026-08-27
updated: 2026-09-07
---

Heather accepts decimal natural-number syntax only. Binary formats and
bitvector-heavy specifications therefore spell bytes such as REX.W, opcodes,
and ModRM as decimal values (`72`, `137`, `216`), hiding the bit layout humans
must review. Hexadecimal and binary source forms should remain ordinary
carrier-directed numerals, not introduce new numeric semantics.

## Acceptance

- Parse at least hexadecimal (`0x...`) and binary (`0b...`) natural literals;
  decide explicitly whether octal belongs in the same round.
- Support separators consistently across decimal and radix forms, with clear
  errors for missing digits, invalid digits, and misplaced separators.
- Feed the parsed value through the existing carrier-directed numeral route
  described by `docs/language/carrier-directed-numerals-design.md`; `0x48` at `Nat` and
  at `BitVec(8)` must differ only through the same existing carrier choice as
  decimal `72`.
- Keep overflow/modular behavior owned by the selected carrier. The parser
  must not impose a host-sized integer limit or a byte-specific rule.
- Preserve the written spelling in diagnostics where useful, while generated
  kernel terms remain the same as for the equivalent decimal literal.
- Add parser, elaboration, computation, malformed-input, and large-literal
  controls. Include representative x86 bytes and bit masks.
- Respelling existing binary-format fixtures is a follow-up readability edit,
  not part of the trusted implementation.

## What it assumes from elsewhere

- **[[carrier-directed-numerals]]** owns how a parsed natural value is resolved
  at its expected carrier. Assumed here: only that radix syntax enters that
  same route.
- **[[x86-64-machine-model]]** is a motivating consumer, not a dependency.

## Log

- 2026-08-27: Filed alongside [[list-literal-syntax]]: list punctuation removes
  the constructor noise from byte strings, while radix literals separately
  expose prefix/opcode/ModRM bit structure for review.
- 2026-09-07: Landed: `0x`/`0o`/`0b` numerals with `_` separators between digits, lexer-level refusals naming the offending character, and the token/AST unchanged (value only) so every carrier route is shared with decimal by construction. Octal included. The u64 token bound is kept in every radix (it was already the decimal form's and the kernel's NatLit's); a wider literal is a separate decision. Written spelling is not carried past the lexer (render_expr prints decimal) — judged not worth touching every Num site. Design: docs/archive/radix-numerals-design.md; controls: crates/syntax/src/lexer.rs tests, crates/elab/tests/radix_numerals.rs. Respelling binary-format fixtures remains the readability follow-up the issue already excludes.

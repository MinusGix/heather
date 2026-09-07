# Radix numerals: design record

Issue: `issues/radix-numeric-literals.md`. Landed 2026-09-07.

## Decision

A numeral has four spellings and one meaning:

```
numeral := decimal | "0x" hexdigits | "0o" octdigits | "0b" bindigits
digits  := digit ( "_"? digit )*
```

- The prefix is lowercase (`0X48` is refused as the decimal `0` followed by
  an invalid digit `X`); hexadecimal digits may be either case.
- `_` may separate two digits and appear nowhere else — not after the
  prefix (`0x_1`), not doubled (`1__0`), not trailing (`1_`). `_1` is an
  identifier, as it always was.
- A numeral ends at the first byte that is not a digit, letter or `_`. A
  letter or `_` that cannot continue it is an error naming that character
  (`0b12`, `0xfg`, `12abc`), not the start of an identifier token. Nothing
  in `lib/` or the tests relied on `12abc` lexing as two tokens.
- Octal is in. It costs one match arm, and leaving it out would have made
  `0o7` lex as `0` followed by an invalid digit — a diagnostic about a form
  the language deliberately lacks is more design than the arm.

The token stays `TokKind::Num(u64)` and the AST stays `ExprKind::Num(u64)`.
A radix form is a *spelling*: carrier choice (`Nat`, `Fin`, `Numeral<A>` via
`ofNat`; `docs/carrier-directed-numerals-design.md`), the emitted kernel
term, and every diagnostic downstream see only the value, so `0x48` and `72`
are indistinguishable past the lexer by construction. The written spelling
survives wherever a diagnostic quotes the source by span; the resolver's
`render_expr` re-prints the value in decimal, and carrying the spelling
through the AST for that one printer was judged not worth touching every
`Num` site. Revisit if a trace ever has to show a byte the way it was
written.

## The bound

The value is bounded by `u64`, in every radix, with the message the decimal
form always had (`numeral out of range: <as written>`). This is the token's
bound, not a carrier's: `bitvec::ofNat` wraps `0x12c` at width 8 exactly as
it wraps `300`, and the kernel's `NatLit` is `u64` already, so the lexer
adds no limit that was not there. A numeral wider than 64 bits is a
separate decision (a bignum literal term), not this round's.

## Controls

`crates/syntax/src/lexer.rs` (tests module) pins the grammar and every
refusal; `crates/elab/tests/radix_numerals.rs` pins the routes — `Nat` by
`refl` against the decimal, `Int` through `Numeral<Int>`, `Fin` through the
index rule with its bound refused, `BitVec(8)` through `ofNat` with x86
bytes (REX.W `0x48`, MOV `0x89`, ModRM `0b11_011_000`) and field masks —
plus the full-width `0xFFFF_FFFF_FFFF_FFFF`, a lexer refusal rendered
through the elaborator, and a wrong-value negative control.

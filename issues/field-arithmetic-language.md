---
title: A field-arithmetic sublanguage with its own compile strategy (Poly1305, X25519)
status: open
labels: [cryptography,native,design,metaprogramming]
area: heather-in-heather
milestone: [hih-crypto]
created: 2026-11-10
updated: 2026-11-10
---

Stage C5 of `docs/native-lexer-crypto-roadmap.md` §4. Poly1305 (mod
2¹³⁰ − 5) and X25519 (mod 2²⁵⁵ − 19) need limb arithmetic: unsaturated
limbs, delayed carries, a reduction that uses the prime's shape. Nobody
should write or prove that code per prime. Fiat Cryptography's answer is a
compiler: a prime and a limb layout in, straight-line word code and its
proof out.

In `docs/compilation-vision.md`'s terms this is a DSL with its own compiler
(§2.2), or equally a `datarepr` of ℤ/p as limbs (§2.4): the question of
which is part of the design.

## Scope

- A design note first: the term language (field expressions over ℤ/p), its
  meaning (`ModEq`, `lib/std/num`), the limb representation and its
  invariant (bounds per limb), the compiler to `rt` terms or FunctionIR,
  and one soundness theorem for every prime of the supported shape.
- `field def Fe25519 = 2^255 - 19 limbs 5 x 51;` as the frontend, in the
  shape of `regex def`.
- Whether `datarepr` covers a quotient specification type
  (`docs/datarepr-design.md` speaks of inductives).
- Constant time by construction: the generated code is straight-line, so
  the `ct fn` judgment ([[native-constant-time]]) accepts it.

## Done when

Multiplication mod 2²⁵⁵ − 19 is generated, certified natively, and agrees
with multiplication in ℤ/p by the language's one theorem, with RFC 7748's
vectors passing on the ladder built over it.

## What it assumes from elsewhere

- **[[x86-wide-multiply-and-carry]]** owns the instructions.
- **[[bitvec-rotates-and-wide-ops]]** owns `mul_wide` and `adc`.

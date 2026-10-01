---
title: Byte comparisons and literals a native step can write and the frontend lowers
status: open
labels: [native,frontend,surface-syntax,function-ir,design]
created: 2026-10-01
updated: 2026-10-01
---

A native program's step still spells byte tests as
`b.unsigned_lt_bit(BitVec::ofNat(10))`, and equality as two nested
comparisons (`wc_l.hthr`'s `newline`, `wc.hthr`'s `space_byte`). The
surface has no shorter form the native frontend recognises:

- `<` is Prop-valued (`Lt`), and no `LinearOrder<BitVec(n)>` exists. `if b < x`
  lowers to a `decide` match on `Or`, which the structured reflection refuses
  (it branches only on a resolved `Bool`).
- `==` is not Heather syntax ("`==` is not used in Heather").
- `10` at `BitVec(8)` has no `Numeral` instance. A char literal is a `Char`,
  and there is no `CharLiteral<BitVec(8)>`.
- The FunctionIR source frontend's only Bool producer is `unsigned_lt_bit`,
  and the x86 lowering has no equality comparison.

The questions are design questions, not plumbing:

- Should a step read Prop-valued comparisons through `decide` (the frontend
  then recognising decision procedures), or should bytes get Bool-valued
  operations under their own names?
- Does equality become an IR node (`sete`) or stay two comparisons?
- What must a literal instance reduce to so the frontend still sees
  `ofNat(width, n)`?

The structured reflection matches the literal head, so an unreduced class
projection would not match.

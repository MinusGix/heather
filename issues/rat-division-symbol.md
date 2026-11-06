---
title: Division symbol at Rat and CReal: proof-carrying or total
status: closed
labels: [surface-syntax,stdlib]
area: mathematics
created: 2026-11-06
updated: 2026-11-06
---

`/` lexes and is designated at `Nat`, `Int`, `BitVec(n)` and `SInt(n)` since
issues/integer-operator-symbols.md (2026-11-06), but not at `Rat`, `CReal` or
the ordered-field classes. `x⁻¹` at `Rat` asks for `x.Apart(0)` (searched by
`h := infer`), while `Rat::recip` is total. So `a / b` could be:

- `a * b⁻¹`, the proof searched like `⁻¹`'s: honest, but `a / b` at an open
  `b` then needs a hypothesis in scope;
- `a * b.recip()`, total with `a / 0 = 0`, as Lean and Mathlib read it, so
  field lemmas carry `b ≠ 0` instead of the term.

Decide, then designate `/` at `Rat` (and `CReal`, whose `⁻¹` is the same
shape) and state `div_eq_mul_inv`. Watch the all-numeral case: `1 / 2` with
no expected carrier is `Nat` division, `0`.

## Log

- 2026-11-06: Minus chose the proof. Done (docs/division-design.md): `a / b`
  at `Rat` and `CReal` is `a * b⁻¹` at a searched `b.Apart(0)`
  (`div_eq_mul_inv` is `refl`), with the field laws. The search reads locals
  (apartness, a sign, `¬(b ≈ 0)` at `Rat`), closed divisors by computation,
  sign rules through `+ * / ⁻¹ ^ - abs` and squares, and last `nlinarith`
  over the hypotheses as a search rule. `ring` reads `/`; `linarith` clears
  numeral denominators (`a / 2 < a`). `CReal` gained `apart_mul`,
  `apart_inv`, `apart_div`. Gaps filed: [[apart-search-arith-leaves]],
  [[sign-goal-views]], [[ring-reads-integer-powers]],
  [[search-trace-goal-display]], [[ordered-field-division-symbol]]; the
  all-numeral `1 / 2` is logged on [[all-numeral-relations-default-to-nat]].

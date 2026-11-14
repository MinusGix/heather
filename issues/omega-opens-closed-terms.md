---
title: omega opens closed calls, products at a successor, arithmetic definitions and word ranges
status: open
labels: [tactics,omega]
area: tactics
milestone: [tac-arith]
created: 2026-11-14
updated: 2026-11-14
---

The linked SHA-256's agreement proofs (PRs #613, #621) bound a typed
`let … = refl` before many arithmetic steps, only so `omega` would read a
term as arithmetic: `size * Succ(k) = size * k + size`,
`Sha2::ending(z, l).len() = Succ(…)`, `x.doubled(0) = x`, the spelled-out
`be_value([b0, b1, b2, b3])`, `zero.toNat() = 0`, and a word's
`toNat_lt_pow` for a word met only in a fact
([[bv-omega-hypothesis-word-bound]]). Minus, 2026-11-14: most proofs should
be nauseatingly simple, ideally with no tactic written.

**Wanted:** before the search, `omega` opens what it is given, each opening
bounded and named in the failure report when the bound stops it:

- a closed call to its numeral;
- a product at a successor (`a * Succ(b)` is `a * b + a`);
- a call whose argument is or computes to a constructor, named at the
  argument's fields (`ending(z, l).len()`, `spelled(Cons(w, rest)).len()`);
- a definition whose body is arithmetic, followed to it
  (`x.doubled(0)`, `be_value([b0, b1, b2, b3])`);
- every word atom at a literal width with its range `toNat(w) < 2^n`,
  from the goal or a fact.

**Done when** the bindings that exist only to open a term are gone from the
SHA-256 agreement modules and `docs/proof-patterns.md` §3 says what `omega`
opens. Design: `docs/omega-measure-reduction-design.md` §22.

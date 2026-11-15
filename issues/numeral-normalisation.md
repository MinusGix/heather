---
title: Evaluate numeral facts at every numeric carrier (norm_num)
status: closed
labels: [tactics,arith]
area: tactics
milestone: [tac-arith]
created: 2026-10-27
updated: 2026-10-27
---

Closed numeric facts have no single tactic. `Rat::ofInt(OfNat(2)) ≈ 1 + 1`,
`Rat::inv_succ(1) + Rat::inv_succ(1) ≈ 1`, `Rat(355, 113) < 4`, a `CReal`
numeral sum, a `Dyadic` comparison: each goes through omega (when the
structure is concrete), through `refl` on a `Bool` verdict, or through a
one-off lemma (`Rat::two_add_ofNat`, `CReal::zero_add_zero`). All-numeral
relations also elaborate at `Nat` silently (`all-numeral-relations-default-to-nat`),
so the carrier is easy to get wrong.

Wanted: a `norm_num`-style tactic that evaluates numeral expressions at every
numeric carrier and proves the resulting `≈`, `=`, `<`, `<=` and `Apart`.

Scope:

- carriers `Nat`, `Int`, `Rat`, `Dyadic`, `CReal` (through `CReal::ofRat`),
  and the float formats, with `+ - * / ^`, `inv_succ`, `abs`, `min`/`max`;
- the proof is either a `Bool` verdict closed by `refl`, as the interval
  checker's are, or the carrier's `respects` laws over an evaluated rational.
  Never conversion over the numbers' representation, which is what makes
  large numerals expensive;
- as a simp-set step inside other tactics, so that `linarith`'s and
  `field_simp`'s numeral side goals close by it.

## What it assumes from elsewhere
- **[[all-numeral-relations-default-to-nat]]**: which carrier an all-numeral relation means.

## Log

- 2026-10-27: Landed `norm_num()` (lib/std/tactic/norm_num.hthr, design
  docs/tactics/numeral-normalisation-design.md). `=`, `≈`, `<`, `<=`, `Apart` and their
  negations at `Nat`, `Int`, `Rat`, `Dyadic` and `Finite(F)` by a `Bool`
  verdict closed by evaluation (`Nat::leb`/`same` underneath, accelerated on
  numerals of any size); at `CReal` through `NumReal` trees
  (lib/std/tactic/norm_num_real.hthr) whose soundness carries the rational
  verdict across `CReal::ofRat`. `norm_num_at(target)` is the step other
  tactics call on numeral side goals. Residue: `Float(F)` values are
  [[norm-num-float-values]]; open goals stay `ring`'s.

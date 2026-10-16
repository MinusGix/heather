---
title: omega(h…): pass facts as arguments instead of hint lets
status: open
labels: [omega,tactics,ergonomics]
created: 2026-10-15
updated: 2026-10-16
---

`omega` reads its facts from the local context, so proofs feed it by binding
lets that are otherwise unused: `let m1 = …; let m2 = …; omega`,
`let pp = x.den_pos;`, `let s = c.left; let e = c.right; omega`. A reader
cannot tell which lets are load-bearing, and a dead one is never noticed or
removed. `lib/std/rat.hthr` is the heaviest example (rat style review, PR #42,
2026-10-15).

`ring(h…)` already takes its facts as arguments. `omega(h…)` should do the
same: the listed proofs join the context for that call only. Whether a bare
`omega` should then stop reading unlisted lets is a separate decision; reading
only the listed facts would also bound its cost by what the proof names
([[omega-relevant-facts-only]]).

## Acceptance

- `omega(e1, e2)` checks each argument as a proof and adds its type to the
  problem, with the same fact reading as a let in scope.
- The rat order laws drop their hint lets in favour of arguments.

## Log

- 2026-10-16: Data point from the regular Cauchy reals (docs/regular-cauchy-reals-round.md, "Cost"). One `omega` over `j <= n`, given two `Nat::max` facts, costs about three times more with three unrelated `Rat` inequalities in scope than without them. `Rat`'s `<=` unfolds to an `Int` inequality over products, so each such fact is still unfolded and inspected before relevance filtering can drop it. In `CReal::lt_respects`, three such calls were most of the declaration's time; `le_trans` chains replaced them. `omega(h…)`, reading only the listed facts, would have made that rewrite unnecessary.

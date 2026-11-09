---
title: ring reads a carrier's - only when it is a + inv(b) by definition
status: open
labels: [ring,tactics,bitvec]
area: tactics
milestone: [hih-passes]
created: 2026-11-09
updated: 2026-11-09
---

`ring` evaluates a difference as `a + inv(b)` (`RingExpr::eval_rel`'s
`RSub`), which is what `Rat::sub` and `CReal::sub` unfold to, so a carrier's
`-` is read only when it is that by definition. `BitVec::sub` is not: it is
its own ripple-borrow pass (`ripple_sub`, one pass where `a.add(b.neg())`
is two), and proofs and emitted certificates name it. At `BitVec(n)` a goal
mentioning `a - b` is reified as a subtraction and the certificate then fails
to convert (`eval_rel(RAdd(RSub(…), …)) = …` against `a - b + b = a`), a type
mismatch rather than a refusal naming the reason.

`BitVec::sub_eq_add_neg` (`bitvec_ring`) rewrites it first today
(`ring_subtraction` in `lib/_tests/std/bitvec/bitvec_ring_tests.hthr`).

## Shape of a fix

`ring` already has the mechanism: a `Definition` fact (`FactKind::Definition`,
`Reifier::edge_image`) makes a term an atom with a proved equation to a
polynomial. A carrier whose `-` does not convert to `a + inv(b)` (one bounded
check at the first difference met) could make `a - b` such an atom, with
`a + inv(b)` as its definition, if the carrier names the law. Where it is
named is the design question: a field of a small class beside
`CommRingOfInt` (`sub_eq: a - b ≈ a + inv(b)`), found by instance search at
the carrier, keeps it out of a naming convention. Until then the refusal
should at least say that `-` is not read at this carrier.

## What it assumes from elsewhere

- **[[machine-words-modular-ring]]** owns the word ring. Assumed here: only
  that `BitVec::sub_eq_add_neg` states the law.

---
title: ring reads a carrier's - only when it is a + inv(b) by definition
status: closed
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

`BitVec::sub_eq_add_neg` (`bitvec_ring`) rewrote it first
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

## Resolution

Closed 2026-11-09. `semiring` has a class `SubtractionLaw<A>(≈, +, -)` with
`neg` and `sub_add_neg: x - y ≈ x + neg(y)`, and the citable
`SubtractionLaw::sub_eq<T>(x, y)`; `bitvec_ring` gives it at every width from
`BitVec::sub_eq_add_neg`. `ring` asks for an instance at the carrier once
(`RelCarrier::sub_law`); where there is one, a difference `a - b` is reified
as an atom with a `Definition` fact citing the law
(`Reifier::sub_through_law`), its definition the polynomial of `a - b` read
as `a + inv(b)`. Carriers whose `-` unfolds to the sum (`Rat`, `CReal`) have
no instance and are read as before. The class is the named law the "shape of
a fix" asked for, not a convention on names.

The probes found a second gap on the way: an `=` whose sides are bare
variables (`h: a = c` at `BitVec(n)`) was refused, because a binder's type
arrives as the record's structure, not `El(BitVec(n))`, and
`identity_equation` counted the carrier's parameters off an `El` spine only.
It now takes them from the declaration (`params` + `valparams`) there.
Probes: `ring_subtraction` … `ring_variable_sides` and the refusal
`ring_sub_not_add` in `lib/_tests/std/bitvec/bitvec_ring_tests.hthr`.

---
title: Binary division so round_rat evaluates at real formats
status: open
labels: [floating-point,mathematics,performance]
area: mathematics
milestone: [math-float]
created: 2026-10-21
updated: 2026-10-21
---

`Format::round_rat` (`lib/std/float/round.hthr`) divides `|num| · 2^q` by
`den · 2^p` with `Nat::div`/`Nat::mod`. Those evaluate through
`Nat::divmod`, a state machine the kernel does not accelerate
(`crates/kernel/DESIGN.md`, acceleration policy: `div`'s state machine is
named as a cost to be answered in the library), so the cost is linear in
the quotient. A binary16 rounding of an ordinary rational already has a
quotient near `2^25`, so the round 2 tests evaluate `round_rat` only on
E2M1-sized values and test the larger formats through `round_dyadic`,
which shifts.

## Proposal

A division whose reduction cost matches its meaning: binary long
division, one shift-and-compare per quotient bit (built from `half`/`leb`
or bit recursion, which are accelerated), with a theorem that it agrees
with `Nat::div`/`Nat::mod` (or directly with the `q * d + r = n`, `r < d`
specification `Format::approx_div` consumes). `round_rat` then switches to
it and `round_rat_correct` follows by rewriting. A wider use is any literal
`Rat` computation that divides.

## Done when

`round_rat` on a binary32 rounding of a literal like `1/3` computes by
`refl` within the suite's rails, and `round_rat_correct` is unchanged in
statement.

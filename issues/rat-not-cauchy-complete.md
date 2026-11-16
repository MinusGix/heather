---
title: Prove the rationals are not Cauchy complete
status: open
labels: [stdlib,mathematics,reals,number-theory]
area: mathematics
milestone: [math-reals]
created: 2026-11-06
updated: 2026-11-06
---

`CauchyComplete` (lib/std/analysis/sequence.hthr) has its consumer
(`Contraction::fixed_point`) and its instance at `CReal`
(lib/std/analysis/real_complete.hthr). The carrier expected not to inhabit
it, `Rat`, is so far only refused for lack of an instance
(`lib/_tests/std/analysis/sequence_tests.hthr`, `rat_fixed_point_refused`).
State it as a `¬` theorem: no function sends every Cauchy sequence of
rationals to a limit.

Plan (docs/library/sequences-and-completeness.md §3):

1. `2.root_floor(n + 1)` is Cauchy at `Rat`, from `Rat::root_floor_regular`.
2. A limit `l` has `l·l ≈ 2`. By `Converges::mul` the squares converge to
   `l·l`, and `Converges::le` against both halves of `Rat::root_floor_spec`
   pins that limit at 2.
3. `l·l ≈ 2` means `num² = 2·den²` with `den > 0`. Over `Nat` that has no
   solution, by descent: `a² = 2b²` makes `a` even, then `b` even, with a
   smaller `b`. The parity lemmas (`Nat::even_or_odd`, `half_add_half`) are
   in nat.hthr. The descent is the irrationality of √2, a theorem worth
   having in `nat.hthr` or `int.hthr` on its own.

## What it assumes from elsewhere

- **[[real-completeness-interfaces]]** owns the capability; this issue only
  supplies its non-instance.

## Log

- 2026-11-06: Filed from the sequences round.

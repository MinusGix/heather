---
title: Saturation as an operation parameter
status: closed
labels: [mathematics,floating-point]
area: mathematics
milestone: [p3109-projection]
created: 2026-11-25
updated: 2026-11-25
---

In the library, saturation is a property of the format: `RoundsTo`
(`lib/std/num/float/round.hthr`) returns the largest finite float on
overflow exactly when the format has no infinity. The design doc's §10
called saturation "a conversion policy… [that] belongs to the arithmetic
rounds", and it never landed. P3109 makes it a per-operation choice beside
the rounding mode ([[float-p3109]]):

- `SatInf`: IEEE overflow (to infinity where the mode says so);
- `SatFinite`: every value past the finite range goes to the extreme finite
  value, infinite inputs included;
- `SatPropagate`: as `SatFinite` for finite values, but infinite inputs
  stay infinite.

OCP's conversions to E4M3 and E5M2 also offer a saturating variant, so this
serves the existing formats as well.

## Shape

A projection is a mode and a saturation, as in FLoPS §3.3:
`RoundsTo(F, mode, x, r)` becomes the `SatInf` case of a relation with a
saturation argument, or saturation is a separate step after rounding to
unbounded exponent range. The second is FLoPS's, and it makes the lemmas
below short. Today's format-driven behaviour is the default: a format
without infinities has only the saturating projections.

## Theorems (FLoPS §3.3, Lemmas 4 and 5)

- Inside the finite range, projection is rounding, whatever the saturation.
- Projection is faithful: the result is `x` when `x` is a float, otherwise
  one of its two neighbours, for every mode and saturation (the extreme
  finite value counts as a neighbour of an out-of-range `x`).
- Past the range, the result is the extreme finite value or the infinity
  of that sign; which one is a per-mode, per-saturation table proved by
  evaluation.

Every existing theorem stated for nearest modes over `RoundsTo` stays
true at `SatInf`; the faithfulness lemma is what lets the EFTs carry over
to the other saturations ([[float-fast2sum-saturated]]).

## What it assumes from elsewhere

- **[[float-p3109]]** owns the P3109 mapping. Assumed here: only the three
  saturation behaviours above.

## Log

- 2026-11-25: LANDED in `lib/std/num/float/project.hthr` (docs/library/float-p3109-design.md §6): `Sat`, `OverUp`/`OverDown`, `sat_up`/`sat_down`, `project` with `Projects`/`project_correct`, `project_in_range` (FLoPS Lemma 4), `project_none` (SatNone is IEEE at a format with infinities), `project_faithful` (Lemma 5), and the unsigned projection with `project_unsigned_nonneg`. Shape differs from the issue's sketch: saturation sits beside `RoundsTo` rather than as its argument, since `RoundsTo` already is SatNone/SatFinite and only the range's edges differ. Not done: projection of infinite inputs (`SatPropagate` differs from `SatFinite` only there); it belongs with the operations on special values.

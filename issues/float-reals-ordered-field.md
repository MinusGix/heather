---
title: Floats over any ordered field - RoundsTo over K, faithful rounding, Placed
status: closed
labels: [mathematics,reals,float]
area: mathematics
milestone: [float-reals]
created: 2026-10-31
updated: 2026-10-31
---

The last item of `float-reals` (docs/floating-point-design.md §5.1, §6),
split from [[float-reals-next]] when its other three items landed.

Every statement in `lib/std/num/float/float_real.hthr` is at `CReal`, and
the error model there is proved twice over: once at `Rat` (error.hthr), once
at the reals through the cut of a rounding interval (`Format::real_error`
and the rest). The design's plan is one statement over any ordered field
`K` (`RoundsTo` over `K`, with `Rat` and `CReal` instances), so that the
two share their theorems, plus:

- **Faithful rounding that always computes**: at a real, return one of the
  two neighbours of an enclosure, with no breakpoint to decide, so it ends
  without the Padé gap of [[exp-log-grid-gap]].
- **`Placed`** (§6): the real's position against the grid, read off an
  enclosure that clears every breakpoint. [[float-round-real-termination]]
  stated its gap against the whole half-unit grid instead (`F.OffGrid`) and
  recorded that per-mode `Placed` is not built until something needs it;
  the `K`-generic `RoundsTo::exists` of §6 is that customer, if it comes.

## Done when

- `RoundsTo` and the error model stated once over an ordered field, with the
  `Rat` and `CReal` theorems as instances, or a recorded decision that the
  duplication is cheaper to keep, with its reason.
- A faithful rounding of an `Enclosed` real that always returns, with its
  theorem, and a probe at a transcendental.

## Log

- 2026-10-31: Done (docs/floating-point-design.md §18).
  - **One relation over `K`.** `Rat::Around(hom, x, P)` (P at every
    rational of an interval around `x`) and `Format::RoundsIn` in
    round_real.hthr, in a section over `K: OrderedField` and
    `hom: OrderedRingHom<Rat, K>`; `RoundsToReal` is its reading at
    `CReal::ofRat_hom`, and `rounds_real_of_rat`/`_rat`/`_respects`/`_unique`
    are one line each over `rounds_in_*`. The interval form, not §5.1's
    pointwise clauses over `K`, is the recorded decision (§18.1: it is what
    the search produces and every transfer reads, and needs no absolute
    value at `K`).
  - **The error model's transfer once.** `Rat::affine_up`/`affine_down`
    and `Rat::err_in_nonneg`/`_nonpos` (float_real.hthr) carry any
    per-rational bound `|R - q| <= u·|q| + e` to a sandwich at `x`;
    `Format::error_in_*`, `relative_in_*` and `faithful_error_in_*` are its
    instances. The `CReal` theorems are readings (`CReal::abs_of_sandwich`);
    `CReal::err_between`, `err_between_nonpos`, `ofRat_le_max`,
    `le_ofRat_min` and `Format::rounds_real_cut` are deleted, and
    `Rat::sides_of_abs`/`_nonpos` state the affine form. The rational error
    model (error.hthr) stays the base: it is grid arithmetic, which `K` has
    not got.
  - **Faithful rounding.** `Format::Faithful`, `FaithfulIn`,
    `FaithfulReal`; the box test (top rounded down at or below bottom
    rounded up, `faithful_box`), `faithful_between`, the search
    `faithful_real`, and `faithful_real_total(e, narrow)` with no `Option`
    and no condition on the real (`down_le_up`: a box narrower than
    `2^qmin` passes). `Format::real_faithful_error` is the directed modes'
    model for any faithful rounding of a real in range. Probes: exp(1) at
    binary32 and binary64, 1 and the midpoint `1 + 2^-24` where rounding
    down and to nearest never end, 1/3's faithful error, the sandwich at
    `Rat::id_hom`, and a negative control.
  - **`Placed` not built** (§18.1): `F.OffGrid` serves correct rounding of
    the reals at hand and faithful rounding needs nothing; a classical
    `RoundsTo::exists` caller would be its customer.

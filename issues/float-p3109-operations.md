---
title: P3109 operations: mixed-format arithmetic through the projection
status: open
labels: [mathematics,floating-point]
area: mathematics
milestone: [math-float]
created: 2026-11-26
updated: 2026-11-26
---

P3109's operations (interim report §4.10, §4.9) take operands in two formats
and a result in a third, `Add<fx, fy, fr, ρ>`: decode both operands to closed
extended reals, compute exactly, project into `fr` with the projection
specification `ρ = (rounding, saturation)`. The library has every piece
(formats, `project.hthr`'s projection, `p3109_codes.hthr`'s codes) but not the
operations; `arith.hthr` is single-format and IEEE-shaped.

## The change

- Mixed-format `add`, `sub`, `mul`, `fma`, `div`, `sqrt` and conversion:
  the exact value of finite operands is a dyadic (or a rational with sticky
  bits for `div`/`sqrt`) whatever their formats, so each is the projection of
  that value into `fr`, with a correctness theorem `Projects(fr, mode, sat,
  exact, result)` read off `project_correct`.
- The report's special-value tables (`ωAdd(+∞, −∞) = NaN`, …) by
  evaluation, and infinite inputs to the projection ([[float-project-infinite-inputs]]).
- The rounding argument as one type covering the IEEE modes, round to odd
  and the stochastic variants, which all are "truncate or step away"
  (`project.hthr`'s `round_dir`, `project_dir_at`), so an operation takes a
  rounding rather than one entry point per kind.
- Tests: the report's operation examples, and an FP8-into-FP32 accumulation.

## What it assumes from elsewhere

- **[[float-p3109]]** (closed) owns the formats, projection and codes
  (docs/library/float-p3109-design.md §§5–7). Assumed here: only
  `Format::project`, `project_dir_at` and `P3109Layout`.

## Log

- 2026-11-26: Landed the core (design §8): `lib/std/num/float/p3109_ops.hthr` with `XReal` and the report's ω tables, `Rnd` (IEEE modes, round to odd, stochastic) with `project_rnd_faithful`, `project_x` with infinite inputs (closing [[float-project-infinite-inputs]]), `op_convert/add/sub/mul/div/fma/neg/abs` over operands in any formats, `op_*_correct` (IEEE-mode results project the exact value) and `project_x_datum`. Remaining in scope: `sqrt` and the elementary functions (§4.10.8–16), whose exact values are not rational; the report's operation examples as tests beyond the tables exercised here.

---
title: TwoSum, the branch-free error-free addition
status: closed
labels: [mathematics, floating-point]
area: mathematics
milestone: [float-eft, math-float]
created: 2026-10-31
updated: 2026-11-01
---

Knuth and Møller's TwoSum: `s = ○(a + b)`, `a' = ○(s - b)`, `b' = ○(s - a')`,
`δa = ○(a - a')`, `δb = ○(b - b')`, `t = ○(δa + δb)` gives `s + t = a + b`
in a nearest mode with no ordering between `a` and `b` (design §19).

## What it assumes from elsewhere

- **[[float-eft-sterbenz-fast2sum]]** owns Sterbenz, `nbr_grid`,
  `rep_on_grid` and `Finite::add_error`. Assumed here: `t`'s exact value is
  `add_error`'s float, so the work is that `a'`, `b'`, `δa` and `δb` are
  exact.

## Notes

The classic proof (Boldo, Graillat and Muller 2017 for the general case)
splits on whether `|b| <= |a|`: if so, `a'` reproduces Fast2Sum's `z`
through `b`, otherwise the roles swap. Each step is Sterbenz or the
representability lemma at the finer operand's grid, which the module already
states in half-units (`Finite::sterbenz_H`, `Format::rep_on_grid`). Overflow
of an intermediate (Boldo et al.'s `a'` can overflow when `s` is the largest
float) needs its own hypothesis or a proof that it cannot happen in binary.

## Resolution (2026-11-01)

Proved as `Finite::two_sum` and `Finite::two_sum_exact` in
`lib/std/num/float/eft.hthr` (design §19), with probes in
`lib/_tests/std/num/float/eft_tests.hthr`. `s` and `a1` round to nearest;
`b1`, `da`, `db` and `t` may round in any mode. The overflow question in the
notes resolved as one hypothesis, `|a + b| <= max`, used only to show `2b`
is a float when `0 <= b <= a`. Each intermediate is named by its equation
(`= Float::Fin(..)`), as in Fast2Sum. For `b1`, `da`, `db` and `t` that
costs nothing (each is shown `Exact`, so finite); `a1`'s finiteness is
assumed, not derived.

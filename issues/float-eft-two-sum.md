---
title: TwoSum, the branch-free error-free addition
status: open
labels: [mathematics, floating-point]
area: mathematics
milestone: [float-eft, math-float]
created: 2026-10-31
updated: 2026-10-31
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

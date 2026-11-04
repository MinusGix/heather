---
title: Kahan's whole-loop compensated summation bound
status: open
labels: [mathematics, floating-point]
area: mathematics
milestone: [math-float]
created: 2026-11-01
updated: 2026-11-01
---

Kahan's compensated summation over `n` floats has error at most
`(2u + O(n·u²))·∑|xᵢ|` (Higham, Theorem 4.8), against the recursive sum's
`γ(n-1)·∑|xᵢ|` (`Format::rec_sum_error`, design §19). Neumaier's variant
(the branch on `|s| >= |x|`) makes every step a Fast2Sum and has the cleaner
statement `|ŝ - ∑| <= 2u·|∑| + O(n·u²)·∑|xᵢ|`.

## What it assumes from elsewhere

- **[[float-kahan-summation]]** (closed) owns the pieces: addition's model
  with no underflow term (`Finite::add_rel_error`), `List::RecSum` and the
  exact step (`Finite::kahan_step`).
- **`float-error`** owns `γ` and `gamma_add`.

## Notes

Design first. Kahan's step is exact only in Fast2Sum's order, which the
algorithm does not ensure, so Higham's proof runs the standard model on all
four operations of every step and tracks the `(1 + δ)` products through the
compensation; the statement needs the trace of `s`, `c`, `y`, `t` as a
relation like `RecSum` and the `O(n·u²)` term made explicit (Higham gives
`2u + O(n·u²)` with the constant from the expansion). Neumaier's variant is
the smaller first target: each step is `kahan_step` in one order or the
other, and the error terms are the exact rounding errors of the `t`s.

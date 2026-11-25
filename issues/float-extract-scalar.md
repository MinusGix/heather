---
title: Rump's ExtractScalar splitting
status: open
labels: [mathematics,floating-point]
area: mathematics
milestone: [math-float]
created: 2026-11-25
updated: 2026-11-25
---

ExtractScalar (Rump, Ogita and Oishi, *Accurate floating-point summation
part I*, SIAM J. Sci. Comput. 2008, Lemma 3.3) splits `x` against a power
of two `σ = 2^i` with `|x| <= 2^-j·σ`:

```
s  = ○(σ + x)
xh = ○(s - σ)
xl = ○(x - xh)
```

all to nearest. Then `x = xh + xl`, `|xl| <= 2^-P·σ`, `xh` is a multiple
of `2^-P·σ`, and `|xh| <= 2^-j·σ`. Applied to every entry of a vector with
one `σ`, the high parts are fixed-point numbers on one grid and add
exactly. That is the basis of AccSum and of accurate dot products, which
the `gpu` and ML milestones would cite.

## Route

`s` and `xl` are Fast2Sum's outputs on `(σ, x)` (`|x| <= σ` gives the
order), so `x = xh + xl` is `Finite::fast_two_sum_exact` and the grid
facts are `nbr_grid` and `rep_on_grid` (`lib/std/num/float/eft.hthr`,
design §19). FLoPS (§5) mechanized it this way for P3109 and calls it the
first mechanized proof.

## Precision one

FLoPS found the fourth property false at precision one: the original proof
has `s = σ` at a midpoint by assuming every power of two has an even
significand, but at `P = 1` ties go by exponent parity
([[float-precision-one]]), so `σ = 2^i` with odd `i` loses the tie. State
the theorem for `1 <= frac`. Once precision one lands, add the `¬` theorem
at a concrete precision-one format as the negative control.

## Then

Rump's AccSum's error-free vector transformation (the high parts add
exactly) as the first customer. Its whole-algorithm bound is a separate
issue when someone needs it.

## What it assumes from elsewhere

- **[[float-eft-sterbenz-fast2sum]]** (closed) owns Fast2Sum. Assumed here:
  only `fast_two_sum_exact`'s statement.

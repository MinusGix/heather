---
title: Square root of a float, correctly rounded
status: closed
labels: [mathematics,floating-point]
area: mathematics
milestone: [math-float]
created: 2026-10-21
updated: 2026-10-31
---

The last operation of `float-arith` (`docs/floating-point-design.md` §7.1,
§14). Round 4 landed add, sub, mul, fma, div and conversion; square root was
left out because its correctness theorem has nothing to state yet, not
because it is hard to compute.

## The statement problem

Every other operation's exact result is a `Dyadic` or a `Rat`, and its value
theorem is `RoundsTo(F, mode, exact, result)` at `Rat`. The square root of a
float is irrational in general, so there is no `x : Rat` to hand to
`RoundsTo`. Two honest ways to state it:

1. **Through the reals** (`float-reals`): `RoundsTo` stated over any
   `OrderedField`, as design §5.1 planned, and the theorem at `CReal` with
   `CReal`'s square root. This needs `float-reals`' transfer and a `CReal`
   square root, neither of which exists.
2. **As a cut at `Rat`**: a relation `RoundsToSqrt(F, mode, x, r)` whose
   clauses are `RoundsTo`'s with every comparison against `√x` rewritten as
   one against `x` (`g ≤ √x` iff `g ≤ 0 ∨ g² ≤ x`; for `f ≤ g` both
   nonnegative, `|f - √x| ≤ |g - √x|` iff `x ≤ ((f + g)/2)²`). It needs no
   reals, but it duplicates `RoundsTo` and every law proved about it.

Option 1 is the design's direction and keeps one relation. Option 2 could
land first if a customer (the Wick survey's norms, say) needs it before the
reals do; then `float-reals` should prove the two agree.

## The computation (either way)

The magnitude in half-units is `⌊√x / 2^(qmin-1)⌋`, an integer square root
of `m · 2^(q - 2(qmin-1))` after making the shift even, and the sticky bit is
"not a perfect square, or a shifted-out bit was set". It needs an integer
square root with a reduction cost per result bit (as `Nat::ldiv` is for
division) and its specification `r² ≤ n < (r + 1)²`, proved in `nat.hthr`
(by hand: `nat` cannot import `omega`). The sign rules are IEEE's: `√-0 = -0`,
`√x` of a negative nonzero `x` is NaN, `√+∞ = +∞`.

## Done when

`Finite::sqrt` and `Float::sqrt` exist with a value theorem in one of the two
forms above, the sign and special-value theorems, and literal tests at
binary16.

## Resolution (2026-10-31)

Done in `lib/std/num/float/arith.hthr`, design §14.1, with neither of the two
forms above: `RoundsTo` reads the exact value only through comparisons with
half-unit grid points, so the value theorem is `RoundsTo` itself at every
rational in `√x`'s cell (`Format::SqrtCell`: on the same side of every grid
point as `√x`, each comparison read through squares). `Finite::sqrt_correct`
proves it in every mode; `cell_iff_approx` shows the cell is exactly what the
rounding reads and `sqrt_witness_cell` that it is never empty. `Nat::isqrt`
with `isqrt_spec` is in `nat.hthr`; sign and special-value theorems and
binary16/binary32 literal tests are in. When `float-reals` lands, the reals'
`√x` lies in its own cell and the statement transfers; the standard model for
a root waits on that.

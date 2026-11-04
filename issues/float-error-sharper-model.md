---
title: Sharper float error model: u/(1+u), exclusive relative/absolute error, exact subnormal sums
status: open
labels: [mathematics,floating-point]
area: mathematics
milestone: [math-float]
created: 2026-10-25
updated: 2026-10-26
---

`lib/std/num/float/error.hthr` states the error of a correct rounding as
`|r - x| <= u·|x| + η` (`Format::error_bound`), with the relative and
subnormal halves as `relative_error` and `subnormal_error`. The Coq
hardware-float survey (`docs/coq-hardware-floats-survey.md` §5.1–§5.2) found
ValidSDP's specification sharper in three ways, each cheap given design
§13's cell picture, plus two results the paper's interval libraries rely on.

## What to prove

1. **The optimal relative bound.** For the nearest modes, `|d| <= u/(1 + u)`
   in the normal range (Jeannerod and Rump, *On relative errors of
   floating-point operations*, Math. Comp. 2018). The worst case is the
   midpoint just above a power of two. The directed modes keep their bound.
2. **The exclusive model.** `∃ d e, |d| <= u/(1+u) ∧ |e| <= η ∧ d·e = 0 ∧
   r ≈ (1 + d)·x + e`: relative or absolute, never both, instead of the sum
   of the two bounds.
3. **Exact subnormal sums.** If `a.add(b)` rounds into the subnormal range,
   it is exact, because both operands are multiples of `2^qmin`. So the
   model for `add`/`sub` has `e = 0`, and summation analyses never pay `η`.
4. **The bound relative to the result**, `|r - x| <= u·|r|`, which design
   §13 left for later.
5. **Outward rounding.** `next_down` of the nearest rounding is at most the
   rounding toward `-∞`, and `next_up` of it at least the rounding toward
   `+∞` (from `next_up_spec`, `rounds_ge_down`, `rounds_le_up`). This is
   what an interval kernel compiled without changing MXCSR cites (survey §4).

## Customers

`float-eft` (Kahan and compensated summation),
[[ml-scalar-refinement]]'s dot products, and
[[dyadic-interval-enclosures]] for item 5.

## Done when

Items 1–4 are in `error.hthr` (with `*_model` corollaries in `arith.hthr`
for `add`/`sub` using item 3), item 5 in `round.hthr`, and literal probes in
`lib/_tests/std/num/float/`.

## Log

- 2026-10-26: 2026-10-26: [[dyadic-interval-enclosures]] landed with its own outward rounding on Dyadic (a shift, design §16), so it does not cite item 5. Item 5 remains the fact a float-based interval kernel (hardware rounding to nearest, then next_down/next_up) would cite.

---
title: Make CReal terms dyadic at the binary rate 2^-n
status: open
labels: [stdlib,mathematics,reals,performance]
area: mathematics
milestone: [math-reals]
created: 2026-10-30
updated: 2026-10-30
---

`CReal`'s terms are unreduced rationals at the rate 1/(n+1). Both costs grow
with use. A sum or product multiplies denominators, so a term's size grows
with the expression's depth. Under the unary rate, k bits of precision means
asking for term 2^k, and read indices multiply as expressions nest: a sum reads
2n+1 and a product (l+1)(2n+2), with `bound` taken from the *unreduced*
numerator of x_0. Correctly rounded `exp`/`log` (`float-reals`,
`float-transcendental`) need 60+ bits, so they need this fixed first.

Make the n-th term a `Dyadic` within 2^-n, so the index is the bit count:

- **Rate 2^-n** (`Rat::inv_pow2`): a sum reads n+1, a product n + 2 + β with
  2^β above both factors (a bit width, not a value), and an inverse reads
  2g + n + c past the gap's start.
- **Rounded terms**: an operation whose exact term is not dyadic, or would
  grow, floors it to n+1 bits (`Dyadic::floor_rat`). Half the rate pays for
  the rounding, so sizes stay at about n + β bits whatever the depth.
- **Proofs stay rational**: `x.at(n) = x.seq(n).rat()`, and every estimate is
  the rationals' lemma library through `Dyadic::rat`, as the float library
  already does.
- **Public statements keep their shape**: `≈`, `<`, `≤`, `Apart`, the
  embedding, the class instances, `Regular`/`Limit` and the interval
  verdicts. `≈` never mentioned the rate (the thread that kept eventual
  `Same` over Bishop's form made this a criterion).

## Acceptance

- `CReal { seq: Nat → Dyadic, regular: … inv_pow2 … }`. Every law, instance and
  client in `lib/` checks on it, and the tactics are untouched.
- `CReal::enclose` reads a term's exact dyadic interval, with no rounding.
- A client test shows a term at a 60+ bit index computed by evaluation.

## Log

- 2026-10-30: Filed by Minus's call in the CReal design thread ("just do
  the full method"). Taken up in the same thread.

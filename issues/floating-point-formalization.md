---
title: Floating point proved against the reals
status: open
labels: [mathematics,reals,floating-point,design]
area: mathematics
milestone: [math-float]
created: 2026-10-20
updated: 2026-10-20
---

Owns the roadmap's `math-float` milestone (`docs/roadmap.md`): binary
floating point in the library, with rounding and error bounds stated and
proved against the reals. Minus has a Lean formalization of floating point
already; the first step is to read it and decide what ports directly and
what Heather should do differently.

Why early inside mathematics: GPU and machine learning both state their
accuracy claims over it, and Minus judges it simple compared with the rest
of the area.

## Questions

1. Which real-number presentation the specification is stated over: the
   regular Cauchy reals of `lib/std/creal.hthr`, or rationals where every
   float is a dyadic rational and the reals enter only in error bounds.
2. Formats as data (precision and exponent range as parameters) or a fixed
   binary32/binary64 pair first.
3. How the bit-level encoding meets `lib/std/bitvec.hthr`, so native code
   can use the same definitions.

## What it assumes from elsewhere

- **[[real-completeness-interfaces]]** owns how the reals' completeness is
  presented. Assumed here: only that a rounding function can be specified
  against an order-complete presentation.
- **[[ordered-field-over-comm-ring]]** owns the ordered-field layer. Assumed
  here: only that error bounds can be stated in it.

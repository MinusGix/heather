---
title: Floating point proved against the reals
status: open
labels: [mathematics,reals,floating-point,design]
area: mathematics
milestone: [math-float]
created: 2026-10-20
updated: 2026-10-21
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

## Log

- 2026-10-20: design proposal in `docs/floating-point-design.md`, after
  reading flean. It answers questions 1–3 provisionally (dyadic values
  embedded in `Rat`; formats as data indexing `Float(F)`; one `encode`/`decode`
  pair over `BitVec`) and lists nine open questions for Minus (§9) and an
  eight-round plan (§8). No code yet.
- 2026-10-20: Minus reviewed the design and agreed with dyadic values, the
  quantum exponent, the mode enum, one `Format` record, payloads and flags at
  the bits layer, and binary only. Classical users get the same theorems
  through constraints that dissolve. `math-float` is rounds 1–5, with
  submilestones `float-values` … `float-transcendental` in the roadmap.
  Notation for the IEEE orders and for rounding is a language-lane ask:
  [[decorated-relation-symbols]].
- 2026-10-20: round 1 (`float-values`) landed on the design PR:
  `lib/std/float/dyadic.hthr` (Dyadic, CommRing and strict order through the
  embedding into Rat) and `lib/std/float/float.hthr` (formats, canonical
  finite floats, `Float(F)` as `Extended`, value order, generic constants).
  What changed from the sketch is in design §10.
- 2026-10-21: `Float(F)` became an inductive with a value parameter after
  PR #89; round 1 merged as PR #85.
- 2026-10-21: round 2 part A (`float-rounding`): `lib/std/float/round.hthr`
  with `RoundsTo` for all five modes, the executable rounding through
  half-units and a sticky bit, its correctness in every mode, sign
  symmetry, `round_dyadic` and `round_rat`. Design §11. Part B
  (successor/predecessor, uniqueness, the mode laws) is next; the transfer
  lemma moved to `float-reals`. `round_rat`'s evaluation cost is
  [[float-round-rat-division-cost]].
- 2026-10-21: round 2 part B, on the same PR: uniqueness
  (`rounds_unique`, through the computed neighbour pair for the nearest
  modes), exactness/idempotence, `next_up`/`next_down` with their
  specification and spacing, `Float::Le`, faithfulness, bracketing and
  monotonicity. Design §12. An inference gap it hit is
  [[value-param-constructor-implicit-inference]].

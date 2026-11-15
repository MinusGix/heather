---
title: Floating point proved against the reals
status: open
labels: [mathematics,reals,floating-point,design]
area: mathematics
milestone: [math-float]
created: 2026-10-20
updated: 2026-11-01
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
   regular Cauchy reals of `lib/std/num/creal.hthr`, or rationals where every
   float is a dyadic rational and the reals enter only in error bounds.
2. Formats as data (precision and exponent range as parameters) or a fixed
   binary32/binary64 pair first.
3. How the bit-level encoding meets `lib/std/bitvec/bitvec.hthr`, so native code
   can use the same definitions.

## What it assumes from elsewhere

- **[[real-completeness-interfaces]]** owns how the reals' completeness is
  presented. Assumed here: only that a rounding function can be specified
  against an order-complete presentation.
- **[[ordered-field-over-comm-ring]]** owns the ordered-field layer. Assumed
  here: only that error bounds can be stated in it.

## Log

- 2026-10-20: design proposal in `docs/library/floating-point-design.md`, after
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
  `lib/std/num/float/dyadic.hthr` (Dyadic, CommRing and strict order through the
  embedding into Rat) and `lib/std/num/float/float.hthr` (formats, canonical
  finite floats, `Float(F)` as `Extended`, value order, generic constants).
  What changed from the sketch is in design §10.
- 2026-10-21: `Float(F)` became an inductive with a value parameter after
  PR #89; round 1 merged as PR #85.
- 2026-10-21: round 2 part A (`float-rounding`): `lib/std/num/float/round.hthr`
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
- 2026-10-21: round 3 (`float-error`): `lib/std/num/float/error.hthr` with
  `ulp_at`/`err_at`, the rounding error in every mode (half an ulp nearest,
  one directed), the standard model in the normal range, the subnormal
  absolute bound `η`, the combined `u·|x| + η` bound, and γ with its algebra
  and the product composition `gamma_prod`. Design §13. An inference gap it
  hit is [[list-literal-left-of-append]] (a method call on a list literal has the same missing carrier).
- 2026-10-21: round 4 (`float-arith`): `lib/std/num/float/arith.hthr` with add,
  sub, mul, fma, div and format conversion on `Finite` and `Float`, each with
  its value theorem in every mode, the IEEE §6.3 signs (one lemma,
  `round_signed_sign`, through every operation), the special-value table and
  the standard model for a finite result. Division rounds through the new
  binary long division `Nat::ldiv`, which `round_rat` uses too. Design §14.
  Square root is [[float-sqrt]] (its statement needs the reals or a cut form
  of `RoundsTo`); binary32 literals wait on [[kernel-wide-run-comparison]].
- 2026-10-25: 2026-10-25: surveyed Coq's hardware floats (Martin-Dorel, Melquiond, Roux, JAR 2023) in `docs/surveys/coq-hardware-floats-survey.md`. Conclusion: no primitive floats in the kernel (they are definition-shape cases plus specification axioms, §2); Heather's executable-plus-relation design is the paper's spec stack without the axioms (§3). Native-lane machine assumptions for the round that first lowers a float op are in §4 (MXCSR as step input, SSE2 only, NaN platform policy, compiler identities at Float(F)). Filed [[float-error-sharper-model]], [[float-conformance-vectors]], [[float-literal-entry]], [[dyadic-interval-enclosures]].
- 2026-10-26: 2026-10-26: interval enclosures over Dyadic and the Expr inequality checker landed, design §16; [[dyadic-interval-enclosures]] closed.
- 2026-10-31: square root ([[float-sqrt]], closed): `Finite::sqrt`/`Float::sqrt`
  with the value theorem stated at every rational in `√x`'s cell (no second
  relation, no reals), `Nat::isqrt` in `nat.hthr`, the IEEE signs and specials.
  `float-arith` is done. Design §14.1.
- 2026-10-31: round 5 begins (`float-eft`): `lib/std/num/float/eft.hthr` with Sterbenz, grid preservation, the nearest addition error and Fast2Sum ([[float-eft-sterbenz-fast2sum]]); TwoSum, TwoProduct, Veltkamp and Kahan filed as [[float-eft-two-sum]], [[float-eft-two-product]], [[float-eft-veltkamp]], [[float-kahan-summation]]. Design §19.
- 2026-11-01: TwoProduct (by fma, off the subnormal grid) and TwoSum (no order between the operands, `|a + b|` in range) land in `eft.hthr` ([[float-eft-two-product]], [[float-eft-two-sum]], closed); Veltkamp and Kahan remain. Design §19.
- 2026-11-01: Veltkamp splitting at normal `x` (`eft.hthr`, [[float-eft-veltkamp]], closed) and, in the new `summation.hthr`, addition's standard model with no underflow term, the recursive sum's `γ(n-1)` bound and Kahan's exact correction step ([[float-kahan-summation]], closed). Round 5 (`float-eft`) is complete; Kahan's whole-loop bound and subnormal Veltkamp are filed ([[float-kahan-bound]], [[float-veltkamp-subnormal]]). Design §19.
- 2026-11-05: gardener: cites a file it shares with [[cast-carrier-reader]] (`lib/std/num/float/arith.hthr`); [[class-inherited-field-implementations]] (`lib/std/num/creal.hthr`, `lib/std/num/float/dyadic.hthr`); [[match-on-proof-call-cost]] (`lib/std/num/float/eft.hthr`).

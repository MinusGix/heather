---
title: calc: equational reasoning chains instead of trans/j towers
status: closed
labels: [frontend,proofs,ergonomics,design]
created: 2026-08-15
updated: 2026-08-18
---



Spun off [[datarepr-surface-ergonomics]] item 6, user-confirmed wanted
(2026-08-15): issues for "tactics we definitely want". The unowned half
of proof verbosity — [[congruence-by-anti-unification]] owns inferring
cong's function; nothing owns the chain itself. Today an equational proof
is a `trans`/`j` tower with fully-spelled motives:

```heather
trans(bin_succ_abs(binc(…)), cong_succ(trans(bin_succ_abs(…), cong_succ(ih))))
```

A calc form (Lean/Isabelle-style: a chain of `_ = rhs { by }` steps,
elaborated to the same trans/j tower) is the single biggest lever on
hand-override certificates — the users the cost basis exists for. Design
should decide how a step names its justification (term? future tactic?)
and how rewriting-under-a-context is spelled (the j-motive question —
this is where it meets [[congruence-by-anti-unification]] and, later,
[[grind-port]]).

## Log

- 2026-08-18: Datum for this issue's value case, measured elsewhere and recorded here so a calc round does not over-claim: putting every step in checking position is NOT what unblocks the library's congruence sites. Of lib/std/num/int.hthr's 54 hand-spelled one-place contexts, 38 fail only because they sit in inference position (which calc would clear) and 16 fail with the expected type already in hand, because the congruence context is a fact about how the two sides COMPUTE and not how they are spelled -- and a calc step states its sides in the same unreduced terms the theorem does. See [[congruence-by-anti-unification]]'s 2026-08-18 entry. Calc's case rests on readability and on hand-override certificates, which is where it was made; it should not also be sold as this.
- 2026-08-18: Round complete (docs/tactics/calc-equational-chains-design.md). The form already existed (2026-07-24 desugaring, endpoints pinned by name since 2026-08-17); this round answered the three open questions and measured what the pieces compose to at HEAD before touching anything. (1) Justification: := expr stays the only form; the seam for [[grind-port]] is that the slot is an ordinary expression in checking position at the step's stated equation -- ?hole in a step raises a goal named/typed by the step, dischargeable by on (measured, pinned by test), and every automation form this surface grows arrives as an expression, so calc needs nothing. (2) Context spelling: terse cong(p) IS the calc-native context -- measured at HEAD, a step is a checking position by construction (named endpoints), so the 2026-08-18 result-only deferral reaches it and the section-1.1 bucket clears inside calc with zero new code; the section-1.2 wall stands inside calc exactly as outside (measured, negative-control test), and the calc-native way through it is the author stating the reduct as a refl step, after which terse cong generalizes (measured, tested). Rejected: hole-in-term contexts, per-step rewrite directives (that is rewrite, layer-m), motive sugar. (3) Other relations: residue, [[calc-over-order-relations]], shape pinned there (per-step relation token folding through a Trans class); not now because no library chain wants it and the kit lemmas lack the named-endpoint shape. No parser or elaborator change landed -- the deliverables are the design record, five composed-behavior tests in crates/elab/tests/operators.rs (checking AND inference position, neutral scrutinees, negative control, the seam), and the readability evidence: eight towers rewritten as calc chains with statements untouched (nat: mul_succ_left, mul_comm, mul_shuffle, pow_mul; int: neg_add's deepest arm, mul_neg_l, mul_assoc's two worst sign cases -- the sym(trans(...)) compositions now read forward). Two-leaf trans(p, sym(q)) one-liners deliberately left alone. Scope guard held: none of this claims the library's congruence sites; the 7/84 arithmetic on [[congruence-by-anti-unification]] is unchanged, plus one new datum logged there (cross-type cong through OfNat hits a convertible-but-unequal annotation spelling).

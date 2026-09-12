---
title: Typed neutral congruence for the eliminators: stop re-comparing annotations well-typedness forces
status: open
labels: [kernel,conversion,performance,design]
created: 2026-09-06
updated: 2026-09-12
---

The 2026-09-06 round made conversion's `app`/`fst`/`snd` neutral rules
typed: heads compared, the head's inferred Π/Σ read, the argument compared
at that domain; the stored annotations are never related to each other
(`crates/kernel/DESIGN.md`, Algorithms; [[function-ir-x86-proof-scaling]]).
The same inheritance from ch. 06's untyped conversion is still in the
remaining neutral arms of `Conv::tm_ne`: two `elim_Wf`s compare shape and
arity (`self.ty(env, s1, s2)`, `tm_at_nat(k1, k2)`), two `elim_Nat`s /
`case`s / `J`s / `transp`s compare motives, branch telescopes and type
components structurally, at every meeting of the two neutrals. On a
Wf-lowered inductive the shape is the sum-of-Σs, so one such comparison is
the size of the declaration.

It did not show on the x86 workload only because record projections are
named globals ([[theorem-field-projection-oom]]); any proof that compares
two neutral matches on one scrutinee — the setoid transfer proofs, the
relational-context certificates — is the shape that pays.

## What is redundant and what is not

- **Redundant** given well-typedness and convertible scrutinees: the
  *shape* and *arity* of `elim_Wf`, the `A`/`B` of `case`, the `I`/`a` of
  `J`/`transp` — all determined by the scrutinee's inferred type.
- **Not redundant**: motives and branches. Two eliminations of the same
  scrutinee may differ there, so they stay compared — but at the *inferred*
  telescope (one `wf_step_telescope` off the scrutinee's type), not at two
  stored copies.

## Acceptance

- Each eliminator arm reads the scrutinee's inferred type
  (`tm_nee_c` + `Conv::delta_to_head_ty`) for every component the typing
  rule forces, and compares only motive and branches.
- The kernel suite, the conv differential oracle and the certgen controls
  are unchanged; measure on a relational-transfer fixture that compares
  neutral matches, not on the x86 module.
- DESIGN.md's Algorithms bullet extended from "application and projection"
  to the eliminators.

## What it assumes from elsewhere

- **[[function-ir-x86-proof-scaling]]** landed the pattern for `app`,
  `fst`, `snd`; this issue extends it and owes nothing back.

## Log

- 2026-09-12: New datum from [[elaborator-canonical-type-spelling]]'s refuted round (docs/record-projection-reference-design.md §9.7): the reused_callee certificate's `Sigma`/`El(?)` bucket — 14,682 misses / 9.16 s, 24.7% of a 37.1 s kernel gate — is the `Fst`/`Snd` *typing* rule reconstituting `Σ(fst_ty). snd_ty` and converting it against the reference `El (app(D#tycode_fn^δ; ā))` the receiver's inferred type carries, once per field read. The elaborator-side fix (spell the read as a reference) was measured and refuted: it moves the compare under evaluation, where chain depth multiplies it. A typing rule that reads the receiver's inferred Σ off its type (the typed-congruence shape this issue already owns for conversion) removes the bucket without moving any read; it is the surviving route and a kernel change, so it waits for a chartered kernel round.

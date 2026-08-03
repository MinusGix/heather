---
title: Ch. 07 obligations for sEq/transp: the with-code FT pass
status: closed
labels: [kernel,delam,metatheory]
created: 2026-08-02
updated: 2026-08-03
---

The [[sprop-strict-prop]] round landed `sEq`/`srefl`/`transp`/`sEmpty` with a
pre-code ch. 07 sketch (`docs/metatheory-ch07-extensions.md` Part III,
§§18–22) whose abort criterion was **not** triggered — but the sketch checked
the global edit for *shape, not in full*. The design doc (§7) carries that as
the round's one standing risk; this issue is where the bill sits, mirroring
[[metatheory-ch07-definitions]] for the definitions round.

## The bill

1. **The evaluation-notion edit, in full.** Part III §19's finding: the strip
   closure cannot be a per-type LR clause (a stuck `transp(e; 5)` at `Nat` is
   a whnf that must relate to `5`), so the LR reads term relations over
   whnf-*then-strip* normal forms — the first extension round to edit a
   shared notion instead of adding cases. The edit touches **every**
   term-relation case; the sketch re-read them for shape only. The FT pass
   walks them all, with the strip premise as *declarative* convertibility
   (§19 finding 2 — the semantic version is circular by levels).
2. **Completeness scoped to the head-only strip.** The 2b acceptance measured
   the gap: `Conv::strip` fires only at the head of a compared term, so a
   stuck-but-strippable transp blocking an elimination spine is invisible —
   `cast ≈ payload` holds while `elim(cast) ≈ elim(payload)` does not. The
   completeness statement must scope the strip's congruence closure
   explicitly, not inherit the TYPES 2024 eager-strip remark (their bundled
   rules backtrack; our per-side loop does not). The gap is confined to
   *redundant* casts (a cast at convertible endpoints is never needed), and
   the 2b generator's rule is to never emit one.
3. **The `sEq(Ty l)` earmark.** An irrelevant equality of codes — a
   definitional observer next to `Id`'s propositional one. Part III §20
   argues it inert (irrelevance collapses proofs, not endpoints; endpoint
   checking still goes through conversion-at-□ = syntactic `==`); the FT
   pass gives it its own line rather than an argument-in-passing.

**Abort criterion, unchanged from the design doc §7:** if the layered LR
cannot state the strip closure without threading relevance marks through
context entries or the congruence rules, the design reverts to the
judgmental sort and `docs/sprop-design.md` gets rewritten.

## What it assumes from elsewhere

- **[[sprop-strict-prop]]** owned the design and kernel round. Assumed here:
  the frozen rule set of `docs/sprop-design.md` and the landed conversion
  behaviours (irrelevance arms, strip loop, endpoint-keyed congruence).
- **[[indexed-families]]** owns the 2b generator. Assumed here: only its
  no-redundant-casts rule, which keeps generated code clear of item 2's gap.
- **[[metatheory-ch07-definitions]]** owns the definitions-round bill over
  the same document (Part IV). No dependency either way; a single metatheory
  round may pay both.

## Log

- 2026-08-02: Filed as the residue owner for [[sprop-strict-prop]]'s
  remaining metatheory scope, so that issue can close.


## Log

- 2026-08-03: CLOSED — the pass is written (managed round), superseding the pre-code sketch: docs/metatheory-ch07-extensions.md Part III is now ~900 lines at Part II's standard, with a provenance table mapping every sketch claim and corrections dated in place. Bill item 1: the sketch's "whnf-then-strip" is CORRECTED — head-only is too weak for the LR (the declarative strip closes under congruence); the notion is one reduction rule (`transp ⇝ₛ payload` under a declarative endpoint-convertibility premise) plus the complementary restriction on ch. 06's proof-reducing congruence, chosen so Determinacy survives verbatim (an unrestricted rule would need confluence, i.e. the termination being proved). All 19 term relations walked: 10 strip-inert by one criterion (a strippable transp is always neutral), 9 load-bearing with one reason each; the edit reaches the type relations for free; cost is exactly one weakened lemma (substitution commutes → joins, consumed only through 07b's Reduction Expansion — flagged as the first thing to re-check before any mechanization). Bill item 2: completeness scoped to derivations using the strip only at the head, with confinement to redundant casts ARGUED via an erasure translation, not asserted; honest limit recorded (redundancy-freedom is not preserved by reduction, so the generator rule is necessary, not sufficient; the residual is always a spurious reject). Bill item 3: sEq(Ty l) inert for four independent reasons, its own section (§20.6). The design doc's §7 standing risk is RETIRED with a stated reason: no equality reflection, so an sEq hypothesis strengthens no convertibility judgment and nothing exists for a relevance mark to mark. One defect found (§22.4): sprop-design.md §5.4 overstated the type-former case — the head-only gap reaches Vec/Fin/El at canonical indices; corrected in place, pinning tests filed as [[seq-strip-type-former-negatives]], generator-rule scope note added to [[indexed-families]].

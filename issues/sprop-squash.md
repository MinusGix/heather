---
title: Squash ∥·∥ and SProp inductives: the restricted eliminator
status: open
labels: [kernel,delam,design]
created: 2026-08-02
updated: 2026-08-16
---

Deferred from [[sprop-strict-prop]] at filing and still wanted: the
user-facing half of SProp. The landed formers serve the generators — `sEq`
carries fording's index equations, `sEmpty` its no-confusion targets — but
the issue's own charter says SProp exists for "evidence that should be
invisible (index constraints, guard predicates, side conditions)", and
squash `∥·∥` is the former that lets a *user* put ordinary evidence behind
the irrelevance wall. Not scheduled; this issue exists so the want has an
owner and the constraints already decided don't get re-derived.

## Scope

1. **Squash `∥A∥`** — the truncation former, with its restricted eliminator
   designed (the part named as "needs designing" at filing): eliminate into
   SProp only, so a squashed witness cannot be observed relevantly. `sEq`
   and `sEmpty` are the special cases that eliminate *anywhere* (equality by
   transport's motive, absurdity vacuously); squash is the general case that
   cannot.
2. **SProp inductives generally** — whether user-declared propositions
   (conjunction, guard predicates) arrive as formers, as squash-of-Σ, or not
   at all. The enumeration invariant makes this a real design choice, not a
   generalization.
3. **Surface `Prop` classification** — elaborator-only, per the dissolved-
   sort decision (`docs/sprop-design.md` §1): the kernel never learns a
   classification; the elaborator owns the policy (as it already owns "`Id`
   is the surface `=`, `sEq` stays generator-internal"). One design section
   here, not a kernel line.

## Constraints inherited, not re-decidable here

- **The irrelevant-former set is closed and enumerated** in
  `docs/sprop-design.md` — extending it (which squash does) is a design
  round with a ch. 07 obligation and a stated abort criterion, wf-former
  discipline, not a patch. Budget yardstick: the sEq round's rec.rs bill
  was 7 branches + five transcriptions.
- **No third sort.** Squash lands as another `Typ` former with an
  irrelevance arm; if its eliminator restriction turns out to *need* a
  kernel-side classification of "lands in SProp", that is the §1 declined
  alternative resurfacing and the design doc's abort framing applies.
- **The kernel has no normal-form readback** (shared invariant with
  [[whnf-sharing-term-growth]]'s round): any design here that wants one is
  an SProp design round with the TYPES 2024 bill attached.

## What it assumes from elsewhere

- **[[sprop-strict-prop]]** owned the base round. Assumed here: the frozen
  design (per-former arms, no sort) and the landed `sEq`/`sEmpty` formers.
- **[[metatheory-ch07-sprop]]** owns the FT pass for the landed formers.
  Assumed here: squash's own ch. 07 case starts from that pass's
  whnf-then-strip evaluation notion, whatever its final form.

## Log

- 2026-08-02: Filed as the residue owner for [[sprop-strict-prop]]'s
  deferred formers, so that issue can close. No round scheduled; promotion
  needs a customer (a guard predicate, a side condition, an existence proof
  a user wants invisible).
- 2026-08-16: Note from the true-prop discussion (2026-08-16): the 'UProp = Prop | SProp' idea — its disciplined cousin is Rocq-style sort polymorphism (definitions quantified over a sort variable). A union sort proper fails on principal sorts (the two sorts differ in conversion via the SProp strip). Currently no customer: kernel Unit eta already gives True judgmental proof irrelevance without SProp, so sort-generic machinery waits for a real demand.

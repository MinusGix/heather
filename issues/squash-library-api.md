---
title: Add the ordinary Squash combinators and exercise them in BoundedList
status: open
labels: [stdlib,logic,proofs,testing]
created: 2026-08-25
updated: 2026-08-25
---

The kernel primitive landed in [[sprop-squash]], but ordinary clients should
not spell its motive and witness branch for every non-dependent use. Add the
small library API derived from `squash_ind`: at minimum `squash_map`,
`squash_bind`, and `squash_join`, with laws that reduce at an introduced
witness. Keep these as ordinary Heather definitions; no new kernel rule or
elaborator recognition belongs here.

The acceptance customer is [[finite-trapping-stack]]. Its `BoundedList`
operations should derive replacement fit evidence through this API where the
operation is non-dependent, and use `squash_ind` directly only where the
dependent motive earns the extra syntax.

## Acceptance

- Add map, bind, and join with useful universe-polymorphic signatures.
- Prove their introduction/beta laws and the basic functor/monad-shaped laws
  that follow by Squash irrelevance.
- Use at least one combinator in `BoundedList`; do not leave the API as an
  isolated logic-module ornament.
- Record any surface friction caused by inferred `squash(a)` or the explicit
  dependent eliminator, rather than adding another primitive pre-emptively.

## What it assumes from elsewhere

- **[[sprop-squash]]** owns the landed former and restricted eliminator.
  Assumed here: only their implemented typing and beta rules.
- **[[finite-trapping-stack]]** owns the container and its laws. Assumed here:
  only that it is the first concrete client of squashed evidence.

## Log

- 2026-08-25: Filed from the implementation review. The primitive is usable,
  but its constant-motive special cases should be ordinary library names.

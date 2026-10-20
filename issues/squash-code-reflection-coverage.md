---
title: Pin surface code analysis of all four Squash constructors
status: open
labels: [elaboration,staging,testing,kernel]
area: language
created: 2026-08-25
updated: 2026-08-25
---

[[sprop-squash]] deliberately made Squash non-magical across the staging
firewall: quoted `Squash`, its type encoding, `squash(a)`, and
`squash_ind(...)` are four distinct code-recursion branches. The kernel
identity recursor exercises all four, but no surface `match code` fixture yet
proves that a Heather analyzer can name and distinguish those branches.

Add a small surface analyzer with a mandatory default arm and one focused
fixture for each Squash branch. Pin both the classification result and the
fact that the quoted introduction exposes the witness syntax to code while a
live `q : ∥A∥` remains irrelevant.

## Acceptance

- A `match code` surface fixture reaches each of `ty_squash`, `tm_squash`,
  `tm_squash_in`, and `tm_elim_squash`.
- The fixture distinguishes introduction from elimination and observes an
  introduced witness's quoted syntax.
- The ordinary live-language negative remains: no test obtains an `A` from
  an arbitrary `∥A∥`.
- Keep the kernel identity-recursion test as the lower-level structural pin.

## What it assumes from elsewhere

- **[[sprop-squash]]** owns the code branches and staging decision. Assumed
  here: only that the four landed branch names are public analyzer syntax.

## Log

- 2026-08-25: Filed after the kernel implementation. Structural recursion is
  covered at core syntax; this owns the missing surface reachability test.

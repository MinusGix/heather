---
title: Decide user SProp inductives and the atomic Squash release bridges
status: open
labels: [kernel,delam,design,sprop]
area: kernel
created: 2026-08-25
updated: 2026-10-26
---

The narrow former in [[sprop-squash]] intentionally stopped before a generic
notion of "this target is SProp". The remaining design question is whether a
real customer needs either:

- user-declared irrelevant inductives, rather than encodings from Squash,
  `Unit`, Π, and suitably irrelevant Σ; or
- atomic release from `∥P∥` into `sEq` or `sEmpty`, which the squash-headed
  eliminator cannot synthesize compositionally.

Do not generalize on resemblance alone. A customer must identify the target
family it needs and why squash-of-existing-formers is inadequate. If only an
atomic bridge is needed, prefer the closed per-former rule whose result shape
the kernel checks directly; a generic classifier or third sort reopens the
larger design bill.

## Acceptance

- Record the concrete customer and the smallest missing elimination route.
- Compare a fixed `sEq`/`sEmpty` bridge, elaborator synthesis for composite
  irrelevant targets, and a generic SProp classification without conflating
  them.
- Preserve the distinction between propositional truncation of a live proof
  and an assertibility/provability predicate over syntax.
- If user inductives land, enumerate their code-recursion and metatheory cost
  before touching the kernel.

## What it assumes from elsewhere

- **[[sprop-squash]]** owns the narrow implemented eliminator and the analysis
  showing exactly where `sEq` and `sEmpty` bite.
- **[[sprop-strict-prop]]** owns the no-third-sort, per-former base design.

## Log

- 2026-08-25: Split from [[sprop-squash]] when its implementable narrow slice
  landed. No current customer forces either bridge or general inductives.
- 2026-10-26: A candidate customer for a third bridge, `∥A∥ → sAcc` (an irrelevant
  accessibility predicate that eliminates into relevant types), is recorded in
  [[squashed-termination-evidence]]: constructive epsilon and countable choice
  types for `math-specific-choice`. It is not a customer for `sEq` or
  `sEmpty`, and it waits on a CCobs-style `cast` before its β rule is usable.

---
title: Proof benchmark: statements with holes, the kernel as the ungameable judge
status: open
labels: [tooling,testing,design,meta]
area: infrastructure
created: 2026-08-05
updated: 2026-08-05
---

From the 2026-08-05 riff under [[ai-facing-tooling]]. Not scheduled —
wants more library first; by then Reals may exist, in which case the
harness disables access to that code before benching.

Harness shape: statements-only files with holes; the model fills bodies;
**kernel-accept is the score** — the untrusted elaborator means no
rubric and no LLM grading, and the benchmark cannot be gamed. Basic
metric: completion rate in a fixed time or context budget.

The richer product is the failure taxonomy, read off the transcripts:

1. **The guidance ladder** — zero-shot vs syntax cheatsheet vs worked
   examples. The minimal winning prompt document is itself a
   deliverable that doubles as human onboarding docs.
2. **Error-message quality** — which diagnostics the model got stuck on
   is a direct measurement; feeds [[ai-facing-tooling]]'s traces.
3. **Feature demand** — what the model reaches for that does not exist:
   the external, adversarial twin of the method that produced
   [[list-algorithms-exercise]]'s still-hurts ranking.

A model with no training-data crutch is the cheapest honest proxy for a
confused new user.

Target sequencing: round one is order/lattice theory (the std order kit
exists; structural proofs; grades smoothly from le_refl to
Galois-connection lemmas). Locales strain the finitary story (frames
want arbitrary joins). Reals are the later round that deliberately
measures the quotient gap.

## What it assumes from elsewhere
- **[[elaboration-determinism]]** owns reproducible elaboration. Assumed
  here: only that scoring wants stable behavior across runs.
- **[[setoid-auto-lifting]]** owns the quotient story. Assumed here:
  only that Reals-shaped targets are blocked on some quotient substitute.

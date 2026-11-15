---
title: Cost as a provable property: investigate calf's phase distinction for Heather
status: open
labels: [semantics,metatheory,design,research]
area: heather-in-heather
milestone: [hih-memory]
created: 2026-09-24
updated: 2026-09-24
---

Investigate cost as a first-class, provable property of Heather programs,
starting from calf (Niu, Sterling, Grodin, Harper, *A cost-aware logical
framework*, POPL 2022; `docs/papers/2107.04663.pdf`) and its successor decalf
(arXiv 2307.05938, not downloaded).

## Why Heather specifically

- calf treats cost as an effect (`step`) and separates behaviour from cost
  with a **modal phase distinction**, with a noninterference theorem:
  input/output behaviour cannot depend on cost. DeLaM is a layered modal
  theory, so the question is whether that phase distinction is another
  modality beside the layers, or already expressible with them.
- `step` is an interaction tree's Tau (`docs/interaction-trees-fit.md`).
  Counting Taus in a fuel-cut tree is a cost semantics for free, so this
  could share one denotation with [[interaction-trees-container-model]].
- The IR's depth fuel and [[memory-bound-certificates]]' metered allocation
  are already cost models, just unnamed ones. Recurrence-relation and
  amortized (physicist's method) proofs would give them a vocabulary.

## Acceptance (an investigation)

A short doc answering: (1) can calf's phase distinction be stated in
Heather without a kernel change (e.g. as a record/modality in the library),
or does it need one; (2) what a cost theorem about a `runtime_fn` would
quantify over: IR steps, x86 instructions, or both, related by a
certificate; (3) one worked example (Euclid or merge sort, as in the paper)
sketched against current `lib/`.

## What it assumes from elsewhere

- **[[memory-bound-certificates]]** owns the space model. Assumed here: only
  that it meters by an explicit budget, which is a cost effect.
- **[[effects-direction]]** owns how effects are denoted at all.

## Log

- 2026-11-05: gardener: cites a file it shares with [[linux-syscall-trace-model]] (`docs/interaction-trees-fit.md`); [[polynomial-functor-interfaces]] (`docs/interaction-trees-fit.md`).

---
title: Would multimodal type theory host a later modality beside DeLaM's layers?
status: open
labels: [kernel,delam,metatheory,research]
created: 2026-09-24
updated: 2026-09-24
---

Investigate whether **multimodal type theory** (MTT) is the right framework
for Heather's modalities if more arrive, above all a *later* modality (▷)
for guarded recursion.

## Why

- DeLaM is already modal (□ over code, the layers). Guarded recursion is the
  principled road to liveness and coinductive reasoning without a
  productivity checker, and it is how Guarded Interaction Trees work
  (`docs/2307.08514.pdf`). calf's phase distinction
  ([[cost-aware-semantics]]) is another modality. Adding them one at a time
  risks three hand-built modal systems.
- MTT gives several modalities from one mode theory, with canonicity, and
  normalization plus decidable conversion (Gratzer 2023).

## Reading

- Gratzer, Kavvos, Nuyts, Birkedal, *Multimodal Dependent Type Theory*,
  LMCS 2021 — `docs/2011.15021.pdf`.
- Gratzer, *Normalization for Multimodal Type Theory* (2023) —
  `docs/2301.11842.pdf`.

## The question to answer

Is DeLaM's layer structure (v < c < p < m, `typeof`, code promotion) an
instance of an MTT mode theory, or does the code recursor's intensional
elimination put it outside MTT? Everything else depends on that. If it is
outside, record what a ▷ beside it would need independently. Consult
`docs/delam/04` first.

## What it assumes from elsewhere

- **[[effects-direction]]** owns whether guarded recursion is wanted at all
  (its 2026-07-31 log lists it as a partiality candidate). This issue only
  asks how it would fit.

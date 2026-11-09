---
title: Wrapped intervals and known bits over words, proved sound once
status: open
labels: [bitvec,native,analysis]
area: mathematics
milestone: [hih-native-heather]
created: 2026-11-09
updated: 2026-11-09
---

The `fits` premises of no-overflow word lemmas and `InBounds` facts are
discharged per site by hand or `omega`; `Ix::hi` bounds only from above
over naturals. `docs/native-mathematics-survey.md` §6; survey rank 6.

## Scope

- Wrapped intervals over `BitVec(n)`, sound under wrap-around and
  signedness-agnostic (Navas, Schachte, Søndergaard, Stuckey, APLAS 2012).
- Known bits (tristate numbers, as the eBPF verifier; Vishwanathan et al.,
  CGO 2022) with `and`/`or`/`xor`/shifts/`add`/`mul` proved sound.
- Both as lattices with transfers for [[dataflow-checked-fixpoints]];
  consumers: `fits`, `InBounds`, alignment (low bits zero), shift amounts.

## Done when

An `InBounds` fact and a `fits` side condition in a compiled tool are
produced by the interval domain, and an alignment fact by known bits.

## What it assumes from elsewhere

- **[[machine-words-modular-ring]]** owns wrap-around arithmetic facts.
- **[[dataflow-checked-fixpoints]]** owns the framework.

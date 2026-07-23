---
title: Implement algorithmic convertibility checking (ch. 06)
status: open
labels: [kernel, delam]
blocked-by: [kernel-reduction]
created: 2026-07-22
updated: 2026-07-22
---

The ch. 06 convertibility judgments, rule for rule: reduce both sides to
WHNF, compare structurally; mutual functions for types / normal types /
neutral types / contexts / terms / normal terms / neutral terms / local
substitutions.

Key shapes to preserve:

- Neutral comparison is an *inference* step returning a type (left-biased;
  ch. 08 shows why that's sound).
- η-directed comparison at all four function types (Pi, UPi, CtxPi, TyPi):
  compare applications to a fresh variable.
- Boxed types/terms compare by syntactic equality (α-equality is free
  under de Bruijn).
- Universe levels compare via level.rs normalization at every annotation
  the rules check.
- Neutral recursors: compare motives + all 13 branches + indices (the
  `C_A` group).
- Layer index restricts types, not terms — conversion at layer p can
  relate layer-m terms at MLTT types (critical property, ch. 06 intro).

Termination is justified by the decidability development (ch. 07/08); the
implementation should take a fuel parameter anyway so the checker is
total-by-construction and a fuel-exhaustion is a distinguishable error.

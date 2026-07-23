---
title: Implement the typing judgments / type checker (ch. 04)
status: open
labels: [kernel, delam]
blocked-by: [kernel-conversion]
created: 2026-07-22
updated: 2026-07-22
---

Syntax-directed checking of fully explicit core terms, mirroring the
ch. 04 judgments: global-context formation, local-context formation and
equivalence, type well-formedness `⊢_i T @ l`, term typing
`⊢_i t : T @ l`, and local-substitution typing — all indexed by layer,
with `typeof(i)` applied where the rules demand it (contexts and types of
layer-v/c/p terms live at layer p).

The heavy corners:

- Layer side-conditions: which rules admit layer v (variables, global
  variables, conversion only); `i' ≤ i` on global-variable use; layer-m
  gating of ULam/box/letbox/recursors/meta-functions.
- The recursor rules: build the branch telescopes (G_M, G_Typ, G_Trm)
  programmatically — 13 branches × (extended Ψ, Γ, L, expected motive
  instantiation). This is the single most error-prone rule; test against
  hand-elaborated instances.
- Non-cumulativity: level equality (via normalization) everywhere, plus
  the explicit level-conversion rule.
- ω discipline: ω appears only as the type level of UPi; reject it in all
  programmer-facing positions.

Endpoint: the milestone in [[end-to-end-compile-instance]] needs this
checker to verify hand-elaborated terms; a nearer smoke test is checking
small MLTT programs at layer p and a tiny letbox/recursor program at
layer m.

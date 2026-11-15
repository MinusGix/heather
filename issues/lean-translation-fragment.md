---
title: Which Lean fragment translates into a predicative Heather
status: open
labels: [translation,metatheory,design,research]
area: lean-in-heather
milestone: [lean-fragment]
created: 2026-10-20
updated: 2026-10-20
---

Owns the roadmap's `lean-fragment` milestone (`docs/roadmap.md`). Minus's
eventual goal is an autotranslator from Lean to Heather (and possibly back)
over a formal model of Lean, in the style of the recent con-leche work, so
that Lean proofs can be cited. It is not first-class Lean support and not a
mathlib import.

The first question is foundational, and the design note answers it before
any code:

1. Lean's `Prop` is impredicative and definitionally proof-irrelevant;
   Heather's kernel is predicative. Which fragment of Lean translates
   directly, and what a translation of the rest would need (a resizing
   axiom, a universe shift, or refusal).
2. Quotients, `Classical.choice` and the other axioms Lean's library uses,
   and how each would be marked through Heather's axiom provenance
   (`docs/kernel/axiom-provenance-design.md`).
3. What formal model of Lean the translator is stated over, and what part
   of the translation is trusted.

## Log

- 2026-11-05: gardener: cites a file it shares with [[squashed-termination-evidence]] (`docs/kernel/axiom-provenance-design.md`).

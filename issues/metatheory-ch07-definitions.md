---
title: Ch. 07 obligations for bodied globals: glueing at p, neutral at c
status: open
labels: [kernel,delam,metatheory]
created: 2026-07-31
updated: 2026-08-05
---



The definitions round ([[simulate-conversion-cost]]) landed bodied global
bindings with **layer-indexed transparency**, and wrote its declarative
rules down (`docs/metatheory-ch07-extensions.md` Part IV, §23–26) but did
*not* machine-check or sketch-check the logical-relations side. The charter
for that round said so explicitly; this issue is where the bill sits.

## The bill (Part IV §26, restated here only as the list this issue owns)

1. **Definitional glueing at p** — the LR interprets a bodied `u` at a
   computing layer by its body, so every place the relation reasons about a
   global-headed neutral gains a case split on whether the global is
   defined.
2. **Neutral at c, and coherence across `□`** — at layer c the
   interpretation is unchanged; the obligation is that the two
   interpretations cohere, i.e. nothing at p reaches through a `box`. This
   is Part I §6's argument re-run one level down.
3. **Fundamental theorem, `u`-cases** — both recursion principles' `u`
   branches and the variable/global cases redo under the split. Ch. 07
   instantiates its generic equivalence twice (ch. 04 declarative, ch. 06
   algorithmic); δ has to be in the first for the second to be complete
   against it.
4. **Termination of δ** — one line off Ψ being a telescope, but it is the
   line that keeps the normalization measure intact.

## What it assumes from elsewhere

- **[[simulate-conversion-cost]]** owns the feature and its rules. Assumed
  here: only that transparency is layer-indexed (δ at p/m, never at c) and
  that a body is checked at its binding's own layer.
- **[[metatheory-ch07-pass]]** is the precedent and the template — Parts
  I–III of the same document, done as pen-and-paper passes.

## When

Same trigger as its predecessor: before the next thing that leans hard on
the LR, or when the Coq formalization is far enough along to extend. The
risk here is bulk, not novelty — none of the four is a new *shape* of
obligation.

## Log

- 2026-08-04: Scope note (2026-08-04): [[generated-term-defs]] landed — the elaborator now emits MACHINE-WRITTEN bodied globals (μ, tag predicates, child projections) alongside user fns. Same obligation kind, more instances: whatever this issue settles for bodied globals covers them uniformly (they are checked and registered exactly as a fn is). The planned successor [[family-types-as-code-defs]] would add layer-c CODE definitions consumed via El at p — check that spelling against ch. 06/07 before that round starts.
- 2026-08-05: 2026-08-05, from [[family-types-as-code-defs]]'s round (docs/family-type-code-defs-design.md §2): the layer-c CODE definitions (D#code : Trm_c(· ⊢ Ty l) := ⌜⟦Skel⟧⌝, consumed as El (D#code^δ) at p) add one case SITE, not one obligation kind — El-of-defined-global is glueing item 1 instantiated at the type interpretation's El case. At p/m the interpretation of El l (u^δ) for bodied u goes through the body via ch. 06's El congruence reduction; at c it is the neutral interpretation, unchanged (the neutral-term global rule admits layer-c globals syntactically at any i ≥ c, 06:558-560). Items 2-4 of the bill cover the new definitions verbatim: a D#code is checked and registered exactly as any bodied global. This answers the 2026-08-04 scope note's question; the spelling was checked against ch. 06 before the round, per that note.

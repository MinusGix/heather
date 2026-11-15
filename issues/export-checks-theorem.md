---
title: State "if it is exported then it checks" over the export language
status: open
labels: [translation,metatheory,design]
area: heather-in-lean-coq
milestone: [export-fragment]
created: 2026-10-20
updated: 2026-10-20
---

`docs/library/export-fragment-design.md` §8 splits the theorem into three lemmas over
HX, the export's intermediate language: (1) Heather → HX preserves typing and
conversion on the fragment, under the eta-long invariant; (2) HX embeds into
PCUIC (MetaCoq); (3) HX embeds into a model of Lean's kernel (Lean4Lean, or
the model the `lean-in-heather` area wants anyway).

This issue owns the *statement*, and lemma 1 first, because it is the only
one about Heather. It belongs beside the kernel's metatheory in heather-coq,
which already states every rule lemma 1 has to map. The work is conversion:
each Heather rule (β, each ι, Π/Σ/Unit η, the irrelevance arms, the strip
rule, δ) maps to an HX rule, and Heather's accelerated evaluation stays out
because it decides the same relation (`crates/kernel/DESIGN.md`, acceleration
policy).

Not started until [[export-library-sweep]] says which fragment matters: a
theorem over formers nobody exports is effort spent in the wrong place.
Rocq's lack of unit η (§5.3) means lemma 2 holds only for the smaller
`F_Rocq`, which the statement should name rather than paper over.

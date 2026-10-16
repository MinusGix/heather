---
title: Ch. 07 obligations for bodied globals: glueing at p, neutral at c
status: closed
labels: [kernel,delam,metatheory]
created: 2026-07-31
updated: 2026-10-16
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
- 2026-09-29: Machine-checked in the Coq formalization (`~/Kairos/Code/Lean/delam`, milestone M9, `M9_DESIGN.md` there; main @ 766b8f8). All four bill items hold for Part IV §23–26's rules, with no admits or axioms. (1) Glueing: δ is a weak-head step, and a defined global's validity is anti-reduction plus its body's validity (`theories/Validity/Delta.v`). (2) Coherence across `□` is structural: reduction never enters `box`, and at c a defined global is inert code. (3) Both fundamental theorems have the defined-global cases; the algorithmic instance is complete against a declarative one that contains δ. (4) Termination comes from normalization, which the relation yields. Departures, all recorded in `M9_DESIGN.md`: an occurrence of a defined `u` carries its body (`gdef u t δ`), so reduction needs no Ψ. The use rule also carries the body's typing at the use layer. That premise is derivable from `⊢ Ψ` (argued there, not proved), and it removes the need for a valid-global-context induction. The carried body is the declared one up to level equivalence, which the Coq Static Code lemma forces. A consequence of keeping `elim(box(u^δ))` stuck ([[opaque-globals-analysis]]'s settled fork): closed canonicity holds at p for global contexts with definitions, but not at m, where that term is a closed neutral. This is not a defect, only a fact to know.
- 2026-10-16: The 2026-09-29 entry's "argued, not proved" premise is now proved (heather-coq `M9_DESIGN.md`, "Follow-up: open item 2", `theories/Typing/DefAdm.v`; heather-coq#19, merged 2026-10-16). The use rule's body premise is derivable from `⊢ Ψ` (`n1_adm`, `n1_adm_eq`: the body is typed at C in its prefix, carried to a level-equivalent body by the Static Code Lemma, lifted to the use layer), so the rules without it are admissible (`wf_gdef_adm`, `eqtm_gdef_adm`, `eqtm_delta_adm`), given only that the carried body has well-formed levels, which a typed occurrence needs anyway. Heather's `u^δ` translates totally (`occ`), with its use, congruence and δ rules derivable (`occ_wf`, `occ_eq`, `occ_delta`). Those three rules are the only ones the two rule sets differ in, so a Heather derivation translates rule by rule; that induction itself waits on an inductive for Heather's rule set (M9's open item 5).

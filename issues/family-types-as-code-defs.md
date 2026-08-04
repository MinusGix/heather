---
title: Generated family types as code definitions (types cannot be Ψ definitions)
status: open
labels: [kernel,elaboration,performance,inductives,design]
created: 2026-08-04
updated: 2026-08-04
---

The successor to [[generated-term-defs]], and the second defect that round uncovered: after routing the generators' *terms* (μ, tag predicates, child projections) through kernel definitions, the residual superlinearity in the forded fixtures is the emitted **types** — a forded family's ⟦Skel⟧ and its index type I are `Type::Wf`s of Θ(constructors) nodes, written out afresh Θ(constructors) times. And the lever does not reach them: `GlobalBinding::Ty` has no `body` field (`crates/kernel/src/term.rs:1005`) — a type cannot be a Ψ definition.

## The shape a fix takes

A **code** definition: `D#code : Trm_c(· ⊢ Type_l)` with the type spelled `El (D#code^δ)`. That is a scheme change, not a mechanism reuse: every structural reader of `Type::Wf` (`spine`, `build_elim_wf`, `const_elim_wf`, `tag_of`) would have to go through `decoded`/whnf, and the fording doc §14.3's "pre-reduced family types are diagnosed, not handled" acquires a much larger surface. Recorded at fording doc §14.11/§14.12.

## What it would answer to

- `forded/computed-arms` residual slope **2.79** and `forded/declared-index-tags` **2.61** (post-[[generated-term-defs]] baseline, 2026-08-04) — the constants fell 4–7×, the exponents barely moved, and this issue owns what remains.
- **Route 1's §10.3** ("large per-occurrence terms"): route 1 did NOT shrink in the def round, because its family IS a type-valued eliminator — there is no per-declaration term to name. This issue is route 1's lever too, and route-1 §10.1's recognizer will need the same look-alike negative discipline (`forded.rs mod fingerprint` is the template).

## Couplings

- [[metatheory-ch07-definitions]]: layer-c code globals are exactly what ch. 06/07's blocking discipline governs; a D#code consumed via El at p while syntactic at c is more of the same obligation kind, but the El-of-def spelling should be checked against the book before the round (read docs/delam ch. 06/07 before recommending a spelling).
- Fording doc §14.3: the pre-reduced-type seam grows; the round that takes this on re-reads that seam first.

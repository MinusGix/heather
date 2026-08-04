---
title: Route generator-emitted terms through kernel definitions
status: open
labels: [kernel,elaboration,performance,inductives]
created: 2026-08-04
updated: 2026-08-04
---

The kernel has had bodied globals with layer-indexed transparency since [[simulate-conversion-cost]] (2026-07-31), and user `fn`s are Ψ-referenced — but the *generator's own artifacts* are still anonymous terms inlined at every occurrence: `μ` (in the family type, twice per Σ projection, several times per arm), the tag predicates, the child projections, the per-arm eliminator instantiations. `docs/inductive-fording-lowering.md` §14.2 and §14.9 both name "a kernel `def`" as the fix; this issue is that slug.

## What it owes

- Emit the per-declaration artifacts (`μ_D`, `is_k`, child projections; whatever else pays) as named Ψ definitions once, references everywhere — the `#skel` namespace precedent for machine names.
- Re-key the recognizers off structure: `forded_of`/`indexed_of` are structural fingerprints (fording doc §14.1, route 1 §10.1) and both seam lists predict a def breaks them with "not a forded family" far from the cause. Name/tag-keyed recognition is part of the design, with negatives.
- Conservativity: δ-unfolding must yield exactly what inlining did — same suite green, deliberate negatives staying negative, axes discipline (open types, neutral scrutinees, ≥3 index constructors, nonzero level).

## The numbers it answers to (frontend bench suite, baseline 2026-08-04)

- `forded/computed-arms` slope **3.39** (31 ms → 1.25 s across 2→6 arms); band 2.60–4.00 records the defect.
- `forded/declared-index-tags` slope **2.65** (§14.9's curve: one more index constructor ≈ doubles every declaration over every family indexed by it); band 1.80–3.00 likewise.
- `forded/occurrences` ~119 ms per use of a forded family.
- `lib/ir_v1.hthr` is 98.8% kernel gate — the frontend hands the kernel a term whose size is a product where it should be a sum.

Expected outcome: the three forded fits fall *below* their bands, `--check` goes red on exactly them, `--save` re-records, and the before/after table in `docs/frontend-benchmarking.md` is the round's number. The §14.9 fuel-cliff negative in `crates/elab/tests/indexed_route_2b_declared.rs` flips positive, and `forded/declared-index-tags` gains its branching row.

## Couplings

- [[metatheory-ch07-definitions]] owns the FT obligations for bodied globals (glueing at p, neutral at c); leaning harder on defs raises its priority but adds no new obligation kind.
- [[frontend-benchmarks]]'s harness is the gate; re-record on a quiet machine first (2026-08-04 baseline is ~1.3–1.5× pessimistic on absolutes; exponents unaffected).
- Route 1's `elim_Wf` families (route-1 doc §10.3) shrink for free; `context-representation-clones` and `schema-construction-caching` are adjacent but not owed here.

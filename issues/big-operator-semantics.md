---
title: "Unify big-operator syntax while deriving semantics from the domain"
status: open
labels: [stdlib,mathematics,notation,research,design]
area: mathematics
created: 2026-08-20
updated: 2026-10-27
---

Design big sums, products, and integrals without prematurely turning each
glyph into an unrelated language feature. The attractive provocation is that
a finite sum and an integral against counting measure are not separate ideas,
and that a rewrite system can exploit evidence that a domain is finite. The
danger is hiding genuinely different convergence, measure, and algebraic
requirements behind notation that only looks uniform.

Separate the shared surface shape from the semantic choice. Compare:

1. distinct library operations under one big-operator binder grammar;
2. generic finite folds for `∑`/`∏`, with integration separate;
3. measure-theoretic integration where finite sums arise from counting
   measure;
4. an expected-type/domain-directed elaboration that selects an operation.

For each, say what elaboration resolves, what typeclass/evidence is required,
what computes on a finite type, and which transformations are definitional
versus named rewrite theorems. “Smart rewriting” must remain predictable:
recognizing `Finite A` may enable a theorem or normalizer rule, but should not
silently change an expression's meaning when a new instance is imported.

## Acceptance

- A design note compares the four routes on finite types, finite sets/ranges,
  countable series, and measure-space integration.
- Concrete Heather sketches cover `∑ i : Fin(n), f(i)`, a finite subset/range,
  and the same sum expressed through counting measure if that route survives.
- State the algebraic structures required for each operator and how empty and
  singleton domains compute.
- State how finiteness is discovered and how instance/scope growth preserves
  elaboration determinism.
- Distinguish parser desugaring, elaborator selection, simplifier rewrites, and
  proved equivalences; no “smart” step remains an unspecified oracle.
- Explain how the design scales to `∏`, `⨆`, and `⨅`, even if only sum and
  integral are implemented first.
- Record dependencies on the chosen real-number and measure foundations.

## What it assumes from elsewhere

- **[[notation-extensibility]]** owns the common big-operator binder grammar
  and symbol classes. Assumed here: `∑` and `∫` can share a surface shape; this
  issue owns what those parsed nodes mean.
- **[[real-number-foundation]]** owns the scalar/completeness basis used by
  analysis. This issue can compare semantic routes before that choice, but
  cannot finalize integration laws ahead of it.

## Log

- 2026-08-20: Filed from the proposal that finite sums should perhaps be
  recognized as the sane finite case of a broader operation rather than as a
  permanently separate construct. The issue keeps that possibility live while
  forcing the resolution and rewrite boundaries to be explicit.
- 2026-10-27: docs/analysis-foundations-design.md §3 recommends route 2 (generic finite folds modulo ≈) for the finite case, with integration defined later as a limit of finite sums (§11); the counting-measure route stays open here. Implementation filed as [[finite-sums-and-products]].

---
title: Use relation and merge notation in the checked proof showcase
status: closed
labels: [syntax,relations,ergonomics,testing]
created: 2026-09-05
updated: 2026-09-05
---

Add curated ≈ and ⊔ tokens with ordinary scoped operator resolution, update editor grammar/highlighting, and use the existing symbolic class-index binders in the checked showcase. ≈ uses the non-associative comparison rung; ⊔ uses left-associative additive precedence. Neither symbol gets a fallback or a global designation. Probe compact-header inference at a finite-set client (the discovered gap is tracked by [[relational-index-inference-from-goals]]), explicit as-binders, scope isolation, and mixed comparison-chain rejection. Named implicit as-binders inside constraints remain owned by [[constraint-index-binder-introduction]].


## Dependencies and boundaries

- [[notation-extensibility]] owns the curated symbol policy.
- [[binder-symbol-as-notation]] and [[operation-indexed-classes]] supply the
  existing scoped bindings; this round adds no resolution rung.
- [[relational-index-inference-from-goals]] tracks the concrete-caller inference
  gap discovered by the probe. A caller with local Mergeable laws succeeds.
- [[constraint-index-binder-introduction]] and [[class-default-operators]] own
  further header and default-notation conveniences.

## Verification

The compact showcase and scoped-law caller check. Missing global meanings and
notation escaping its declaration are rejected. The editor corpus, positive
fixtures, highlighting queries, and inventory passed on Furnace; the showcase
also passed an independent CLI check. Final plain `furnace run -- scripts/test`: 2,351 passed, 0 failed, 5 ignored (426 seconds). All 35 setoid/generator/notation tests and the new precedence/chain parser test passed.

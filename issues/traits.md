---
title: Traits and instances: classes as records, disciplined resolution, programmable later
status: open
labels: [frontend,syntax,elaboration,design,metaprogramming]
created: 2026-08-07
updated: 2026-08-07
---

The general typeclass/trait feature, designed 2026-08-07 in discussion; the full record is docs/traits-design.md and this issue owns its staging (doc §13). One-paragraph contract: a class is a parameterized record; an instance is a namespace of ordinary declarations plus an assembled record value (block and literal forms, `instance Monoid<Rat>`, no `for`); `extends` is flattening plus ONE CANONICAL VALUE PER (CLASS, CARRIER) — parents filled by reference when declared, synthesized as projections when not, overrides owing kernel-checked agreement proofs; resolution is an ascending-scope, deterministic, mode-directed, structurally-terminating backchainer whose every derivation is minted as a canonical named global (memoization = canonicalization), scheduled on the withheld-obligation machinery, failures returning the search trace as data; instance implicits are the default case of solver-default arguments (`:= infer`); layer 3 re-implements the resolver as a heather function over QUOTED goals when context computation lands.

## What it assumes from elsewhere

- **[[compile-typeclass-design]]** owns the Compile certificate shape and CallCtx. Assumed here: only that an instance's semantics stays 'ordinary record value'. Its §5 class layer is superseded by this design (target indexing struck — doc §10).
- **[[elab-unifier-completeness]]** owns the withheld-slot scheduler. Assumed here: only that deferral-and-retry-to-fixpoint stays available to new obligation kinds.
- **[[generators-in-the-language]]** owns the meta-layer migration and the ch. 07 missing-features list. Assumed here: only that context computation is on that list and enumerable.
- **[[elaboration-determinism]]** (closed, spine recorded on [[parallel-checking-and-caching]]): the resolver must be a deterministic function of (goal, scope).
- **[[ai-facing-tooling]]** owns failure-state-as-data. Assumed here: only the direction.

## Staging

Doc §13: (a) layer 1 declaration forms; (b) layer 2 resolver + `:= infer`; (c) trace-as-data diagnostics; (d) layer 3, behind the meta-layer roadmap. Open questions in doc §12 (termination default's bite, post-hoc registration, mode syntax, canonical-table scope, agreement-proof form).

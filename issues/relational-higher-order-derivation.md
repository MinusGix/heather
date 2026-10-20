---
title: Generate proofs through heterogeneous and higher-order relational contexts
status: open
labels: [setoids,design,backlog]
area: tactics
created: 2026-09-05
updated: 2026-09-05
---

The native derivation path primarily uses one homogeneous Type<0> relation, with a special Boolean choice rule. The mathematical transfer core has a broader remit; this issue owns consuming those rules automatically.

## Acceptance

- Accept explicit relation choices at intermediate carriers; do not infer sequence, multiset, or set semantics from a raw List type.
- Compose heterogeneous operations and derive a higher-order map or fold example using certificates for function arguments.
- Preserve distinct left/right implementations, partial application, and relation parameters under binders.
- Validate one mixed chain such as set semantics to duplicate-free enumeration modulo permutation to length modulo identity, with the enumeration assumptions explicit.
- Identify universe restrictions accurately; coordinate varying fibers with the dependent owner rather than flattening them into this fragment.

Proof rules remain owned by [[relational-transfer-core]], per-function universal relational statements by [[certified-parametricity]], and dependent contexts by [[dependent-relational-transport]]. Related: [[setoid-auto-lifting]].

## Scheduling

Captured for a future concrete driver; not scheduled by this filing. See [[setoid-roadmap-and-resumption]].

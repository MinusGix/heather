---
title: Calculate with a locally selected setoid relation
status: closed
labels: [frontend,proofs,setoids,ergonomics]
created: 2026-09-05
updated: 2026-09-05
---

The abstract finite-set client needs calc chains over its locally bound ≈ relation. Lower homogeneous chains to ordinary Transitive evidence, check every written endpoint including single-step chains, and retain native equality behavior. Reject mixed chains until their composition rules are specified. Customer: docs/showcase/finite_set_client.hthr. Related: [[calc-over-order-relations]], [[setoid-auto-lifting]], [[finite-set-client-design]].

## Log

- 2026-09-05: Implemented homogeneous locally bound ≈ chains using ordinary relation_exact/relation_step proofs. Focused tests pass for multi-step Transitive-only chains, single-step endpoint checking, missing evidence, and mixed-chain refusal. The abstract finite-set client uses the syntax throughout.

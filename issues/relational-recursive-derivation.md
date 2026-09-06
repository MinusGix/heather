---
title: Derive recursive compatibility from constructor cases and induction evidence
status: open
labels: [setoids,design,backlog]
created: 2026-09-05
updated: 2026-09-05
---

Transparent unfolding is not a general proof of recursive compatibility. The independent tree backend supplies concrete branching-induction obligations; the list backend supplies a linear control.

## Acceptance

- Start from an explicit relational signature and a supported recursion scheme. Generate checked induction obligations for constructors and recursive calls.
- Derive an image membership characterization or compatibility theorem over both lists and branching trees, preserving source witnesses.
- Consume supplied rules for opaque callees, and report unsupported recursion or missing constructor facts as such.
- Include changed recursive arguments, an invalid observation, and a branch needing a user lemma. Keep termination evidence distinct from relational compatibility.

Do not treat pointwise list parametricity as finite-set semantics. Customers: `tree_image_source` and `tree_image_respects` in `lib/std/tree_finite_set.hthr`. Related: [[certified-parametricity]], [[relational-transfer-core]], [[setoid-auto-lifting]].

## Scheduling

Captured for a future concrete driver; not scheduled by this filing. See [[setoid-roadmap-and-resumption]].

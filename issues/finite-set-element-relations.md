---
title: Compose finite-set semantics with an equivalence on elements
status: open
labels: [setoids,design,backlog]
area: mathematics
created: 2026-09-05
updated: 2026-09-05
---

Both implemented finite-set backends currently compare elements by native identity. Test the next layer explicitly: collections whose elements have different representations of the same mathematical value.

## Acceptance

- Specify membership, singleton, extensionality, and image laws relative to a chosen element relation.
- Require element-map compatibility for image, including a heterogeneous target element relation. State what happens to membership witnesses.
- Use two non-identical equivalent element representations and reuse a meaningful abstract client on both collection backends.
- Reject an element observation that distinguishes those representations; do not replace native identity globally or hide the extra relation choice.

Choose the actual element domain when a driver needs it; unreduced rationals are a candidate, not a prerequisite. Related: [[setoid-core-api]], [[relational-transfer-core]], [[finite-set-client-design]], [[dependent-relational-transport]].

## Scheduling

Captured for a future concrete driver; not scheduled by this filing. See [[setoid-roadmap-and-resumption]].

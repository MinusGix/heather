---
title: Specify finite enumeration and lawful finite-set observations
status: open
labels: [setoids,design,backlog]
area: mathematics
created: 2026-09-05
updated: 2026-09-05
---

The FiniteSets laws describe extensional set algebra but do not themselves establish finiteness. List and tree implementations are finite; cardinality, deduplicated enumeration, and arbitrary folds do not follow from the current abstract interface.

## Acceptance

- Add an explicit finite coverage/enumeration capability only when a client requires it, with executable witnesses distinguished from squashed existence.
- Separate folding raw representatives under duplicate-insensitive algebraic laws from folding duplicate-free enumerations under weaker laws.
- State the decidability or other evidence needed for deduplication and cardinality; relate alternate enumerations at the correct relation.
- Prove representation independence for one requested observation and retain raw length as a negative control.
- Keep endofunction image, heterogeneous image, and enumeration capabilities distinct when their assumptions differ.

Related: [[finite-set-client-design]], [[relation-indexed-algebra]], [[relational-higher-order-derivation]], [[subtype-transfer-and-evidence]]. This is a client capability issue, not a requirement to complete a finite-set library before other work resumes.

## Scheduling

Captured for a future concrete driver; not scheduled by this filing. See [[setoid-roadmap-and-resumption]].

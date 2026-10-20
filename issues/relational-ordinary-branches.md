---
title: Derive compatibility through ordinary Boolean branches
status: open
labels: [setoids,design,backlog]
area: tactics
created: 2026-09-05
updated: 2026-09-05
---

`rel_derive` currently recognizes the resolved `relation_function::choose` combinator. Users should be able to keep an ordinary Boolean `if` or `match` in a function.

## Acceptance

- Reconstruct the same checked branch rule from resolved Boolean elimination, preserving binder scope and source locations.
- Reuse a supplied observation-stability certificate; expose the missing certificate as a resumable goal.
- Cover fixed conditions, input-dependent conditions, nested branches, and local bindings. Include a representation-sensitive condition that cannot be justified.
- Preserve shadowing and distinguish unsupported dependent elimination from a missing mathematical premise. No recognition by source spelling alone.

This is same-choice Boolean support; differently chosen branches belong to [[relational-cross-branch-proofs]]. General recursion belongs to [[relational-recursive-derivation]]. Customer: `docs/showcase/derive_set_functions.hthr`. Related: [[named-function-compatibility-derivation]], [[setoid-auto-lifting]].

## Scheduling

Captured for a future concrete driver; not scheduled by this filing. See [[setoid-roadmap-and-resumption]].

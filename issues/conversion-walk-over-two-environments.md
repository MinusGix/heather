---
title: The lockstep walk stops at closures whose bodies read their environment
status: open
labels: [kernel,conversion,performance]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

[[conversion-closed-pair-memo]]'s walk compares two spellings on the syntax
when both are closed, or when both are read in the query's own scope. A
closure whose body reads its environment (a family's body under its
arguments, a definition's body under a substitution) is still evaluated
node by node. In `grind::by_diseq` about an eighth of the pairs `Conv::ty`
was entered on were of this kind.

The walk generalises: two syntactic closures `(ρ₁, A)` and `(ρ₂, B)` whose
bodies show one former have components `(ρ₁, Aᵢ)` and `(ρ₂, Bᵢ)`, and a
binder extends both environments with the one fresh variable, which is what
the normal-form arm does after evaluating. Leaves (a variable, an
application) go to the domain as closures over the environments reached.
The closed-pair table does not apply: an open pair's verdict is a fact about
the two environments as well.

## Acceptance

- A count first, on the showcase: fuel spent under `Conv::ty` entries whose
  closures are syntactic and not closed.
- The walk over two environments has the tests `conv/spelled_tests.rs` has
  for the closed one, and the differential suites pass.

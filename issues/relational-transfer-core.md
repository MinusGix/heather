---
title: Build a heterogeneous relational transfer core
status: open
labels: [stdlib,relations,transfer,design]
created: 2026-09-04
updated: 2026-09-04
---

Make heterogeneous relations the common vocabulary for setoids, subtype
lifting, implementation correspondence, and proof-producing parametricity.
Keep this an ordinary, small mathematical API with explicit evidence first.

## Scope and acceptance

- Define the respectful function relator, schematically
  `(R ⇒ S)(f, g) := ∀ x x', R(x, x') → S(f(x), g(x'))`, allowing different
  carriers on the two sides. Recover `PreservesRelation` as self-relatedness.
- Derive identity/application/composition rules and curried multiargument
  signatures. Exercise products and lists, including a higher-order `map`
  rule, without requiring one relation per carrier.
- Supply the directional rules for proposition transfer and quantifiers.
  Make coverage and preservation/reflection assumptions explicit: a partial
  correspondence may transfer only restricted quantifiers or implications.
- Keep relations Type-valued. Logical implication/equivalence of propositions
  is not automatically an equivalence of proof objects or types.
- Distinguish a relation and its coverage proofs from constructive maps or
  witness-producing data usable to synthesize operations. Do not silently
  extract representatives from squashed existence.
- Reuse existing relation vocabulary instead of creating a second composition,
  converse, graph, or pullback library. Keep heavy law machinery out of the
  lean execution-semantics dependency path.

## What it assumes from elsewhere

- **[[relation-property-structures]]** owns relation laws and existing pullbacks.
- **[[relational-semantics-refinement-kit]]** owns basic relational combinators.
- **[[relation-combinator-shape]]** owns their eventual uniform surface shape.
- **[[setoid-core-api]]** owns the equivalence-relation specialization.
- **[[setoid-morphisms-and-transport]]** owns mathematical transport customers.
- **[[dependent-relational-transport]]** owns dependent fiber machinery.

Reference guide: `docs/setoid-transfer-references.md`.

## Log

- 2026-09-04: Filed from the setoid and general transfer design discussion.
- 2026-09-04: The function-relator foundation and PreservesRelation specialization are implemented by **[[manual-mergeable-round]]**; container relators, quantifier transfer, and other acceptance remain here.
- 2026-09-04: The next context-construction slice adds explicit constant and dependent-on-input function application certificates, plus a self-related binary helper, in `std/relation_context`. `docs/showcase/relational-contexts.hthr` exercises nested and repeated occurrences. See `docs/relational-context-round.md`; automatic context discovery and relational calc remain open. The constructors are transparent functions so proof-relevant evidence can compute. Focused validation: 7 passed. Final plain Furnace suite: 2,322 passed, 0 failed, 5 ignored.

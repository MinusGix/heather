---
title: Let `rewrite` rewrite along relations, not only `=`
status: open
labels: [frontend,elaboration,proofs,setoids,relations]
area: tactics
milestone: [tac-general]
created: 2026-10-21
updated: 2026-10-21
---

`rewrite(h, e)` takes only proofs of `=`; a relation proof is refused with a
pointer to `rel_cong`/`calc`. Most `Rat`/`CReal` rewriting is along `≈`, and
the interaction-tree laws through `Vis` are stated up to depth-indexed
equivalence ([[interaction-trees-container-model]]),
so their proofs will rewrite along relations too.

Wanted: when `h` proves `R(a, b)` for a relation with the compatibility
evidence `relational_context` already consumes (`Respects2`,
`PreservesRelation`, reflexivity for fixed parts), `rewrite(h, e)` rewrites
`a` to `b` in a goal that is itself a relation application (or `↔`/`→` of
ones), leaving the same missing-evidence obligations `rel_cong` raises. This
is setoid rewriting (Rocq's `setoid_rewrite`, Lean's `grw`). Direction and
occurrence controls come from [[relational-rewrite-controls]] and
[[rewrite-pattern-occurrences]]; a symmetric step still needs explicit
symmetry evidence.

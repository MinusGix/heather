---
title: Let `rewrite` rewrite along relations, not only `=`
status: closed
labels: [frontend,elaboration,proofs,setoids,relations]
area: tactics
milestone: [tac-general]
created: 2026-10-21
updated: 2026-10-26
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

## Log

- 2026-10-26: Design reference: docs/mengine-survey.md §4.3. mengine (and Gross et al. 2023 before it) makes setoid-style rewriting linear by rewriting bottom-up with one congruence step per changed node, chained by transitivity, and a node memo keyed by (equation, context, node) kept across calls. Today's `rewrite` abstracts the goal by a tree walk and costs 2^k on a let-shared goal (survey §4.2), so build this one bottom-up from the start. Under binders, use the pointwise relation and a binder `Respects` instance; mengine uses funext, which Heather does not assume. Bench families with linear lower bounds: [[tactic-scaling-bench-families]].
- 2026-10-26: landed (docs/equation-rewrite-design.md §9). A proof whose type
  as written is a relation application `R(a, b)` (and does not unfold to an
  `=` of its own sides) is a relation step: goals `S(l, r)` and `P → Q` of
  ones, `in := hyp` forward, chains with `=` steps. The walk is bottom-up with
  a node memo (one congruence step per changed node, `Respects2` /
  `PreservesRelation`, reflexivity for the unchanged argument, transitivity
  joins), so a let-shared goal costs linear (bench
  `rewrite/setoid-let-addr0`). Missing evidence raises rel_cong's goals
  (`?compatibility`, `?symmetry`, …). The `=` rewrite's 2^k on let-shared
  goals was the kernel's abstraction walk, now memoised per node
  (`let-addr0` is polynomial). Probes: `lib/_tests/std/num/rat_tests.hthr`,
  `lib/_tests/std/algebra/algebra_rel_tests.hthr`. Left for later:
  [[rewrite-setoid-under-binders]], [[rewrite-setoid-iff-goals]],
  [[rewrite-setoid-heterogeneous]], [[rewrite-every-instance]]; the cached
  path walks let-shared terms as trees in the image code,
  [[image-tree-walks-let-shared-terms]].

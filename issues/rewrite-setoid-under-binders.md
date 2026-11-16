---
title: Rewrite along a relation under binders, through the pointwise relation
status: closed
labels: [setoids,relations,tactics,proofs]
area: tactics
milestone: [tac-general]
created: 2026-10-26
updated: 2026-10-28
---

`rewrite(h, e)` along a relation ([[rewrite-setoid-relations]],
`docs/tactics/equation-rewrite-design.md` §9) walks applications only. An occurrence
of the left side inside a λ is refused, naming the λ: rewriting there would
leave half the occurrences behind otherwise. The `CReal` library is where this
bites first: a sequence `λ n => x(n) + 0` is a λ, and its laws are stated
pointwise.

Wanted: under `λ z. t`, rewrite `t` at the extended context and relate the
two λs by the **pointwise** relation, `Pointwise(R)(f, g) := (z: D) → R(f(z),
g(z))`, then cross the binder's consumer with evidence that it respects
`Pointwise(R)` (a `PreservesRelation(Pointwise(R), S, lim)`-shaped instance),
as Rocq's `setoid_rewrite` does with `pointwise_relation`. mengine crosses
binders with funext, which Heather does not assume, so this is the route.

Design questions this owns:

- where `Pointwise` lives (`relation_props` beside `Respectful`, which is its
  dependent-codomain cousin) and whether `Respectful(RelId, R)` already is it;
- the walk's memo below a binder: results are per node *and depth*, as the
  kernel's node memo keys them, and an occurrence's pattern and proof are
  shifted once per depth;
- an occurrence that mentions the bound variable (`x(n) + 0` with the law
  `(y) → y + 0 ≈ y`) is an instance per binder, so instantiation (§6.1) has to
  happen below the binder, not once at the root.

## What it assumes from elsewhere

- **[[rewrite-setoid-relations]]** owns the walk, the plan and the evidence
  lookup. Assumed here: only that a node's result is `(term, proof)` and that
  evidence statements are elaborated as text over aliases.

## Log

- 2026-10-27: A second customer: `∑ k < n, e` / `∏` (MonoidRel::range, big_operator.hthr) is a λ under a call. Its crossing evidence is `MonoidRel::range_cong` (pointwise below the bound, a bounded Pointwise), not plain Pointwise; setoid rewrite and rel_cong refuse inside a sum today ([[tactics-and-big-operators]]).
- 2026-10-28: Done (docs/tactics/equation-rewrite-design.md §10). `Pointwise<D, C>(R)` lives in `relation_props` beside `Respectful`; `Respectful(RelId, R)` is not it (a transport per point). A λ's body is rewritten one binder down and the λs related by `λ z. p`; nested λs by `Pointwise(Pointwise(R))`. The consumer crosses by `PreservesRelation(Pointwise(R), R, λ g. f(…, g, …))`, found by resolution: for `∑`/`∏`, the evidence rules `MonoidRel::range_pointwise` and `antidiag_pointwise` (braces-only, outside the section: rules take no class premise and instance heads cannot key on a λ); the bounded `k < n` of `range_cong` is dropped. Memo per node and binder scope (per λ node: same depth may bind different types); pattern and proof shifted once per depth; unapplied laws instantiate below binders, the instance kept relative to the innermost binders it mentions. Evidence for a context mentioning no bound variable is resolved once at the root and shifted; otherwise stated below the binders, and a missing one is an obligation closed over them (`(z: Nat) -> PreservesRelation(…, g(z))`). Left: [[rel-cong-under-binders]], [[rewrite-class-law-instantiation]] (why the library's `range_cong` proofs stay). Also fixed in passing: the goal-context printer dropped the parentheses of a function domain (`(Nat -> Nat) -> Nat` showed as `Nat -> Nat -> Nat`).

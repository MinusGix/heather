---
title: Let rel_cong and rel_derive cross binders through the pointwise relation
status: closed
labels: [setoids,relations,tactics]
area: tactics
milestone: [tac-general]
created: 2026-10-28
updated: 2026-10-28
---

`rel_cong(h)` (`crates/elab/src/relational_context/proof.rs`) walks the goal's
two sides in lockstep and stops at a λ: `∑ k < n, c * x ≈ ∑ k < n, c * y`
from `h: x ≈ y` is refused, though `rewrite(h, …)` now proves it
([[rewrite-setoid-under-binders]]).

Wanted: two λs `λ z. a`, `λ z. b` walked below the binder to a pointwise
proof `λ z. walk(a, b)`, and the consumer crossed by the evidence the rewrite
asks for, `PreservesRelation(Pointwise(R), R, λ g. f(…, g, …))`
(`MonoidRel::range_pointwise` for `∑`).

## What it assumes from elsewhere

- **[[rewrite-setoid-under-binders]]** owns `Pointwise`, the crossing
  statement and the sum's rules. Assumed here: only that the statement is the
  one `docs/equation-rewrite-design.md` §10.2 gives.

The builder generates source text over aliases made at the goal's depth, so
the part to design is aliases below a binder (the rewrite states such
evidence in an extended context and keeps nothing, §10.4).

## Log

- 2026-10-28: Done (docs/equation-rewrite-design.md §10.6). `rel_cong`/`rel_derive` cross an application whose sides differ in one argument, a λ on each side: the λs' shared binders give `Pointwise(…(R))`, the consumer's evidence is §10.2's `PreservesRelation(Pointwise(R), R, λ g. f(…, g, …))` (so `MonoidRel::range_pointwise` answers both tactics), and the proof argument is `λ z…. p` with `p` the bodies walked below the binders. Aliases below a binder: the builder pushes the binder, walks and elaborates the body's text *there*, restores its context, and aliases the resulting λ term at the outer depth, so nothing that mentions the binder survives; missing evidence is closed over the binders and applied back (§10.4's obligation shape). Probes in `lib/_tests/std/algebra/big_operator_tests.hthr` (nested, triangle, antidiag, open semiring, bound-mentioning context with and without `on ?compatibility`, an unexplained change refused, `rel_derive` through a sum).

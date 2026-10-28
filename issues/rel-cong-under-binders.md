---
title: Let rel_cong and rel_derive cross binders through the pointwise relation
status: open
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

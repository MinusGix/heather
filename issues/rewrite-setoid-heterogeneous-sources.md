---
title: More sources for the relation a rewrite carries out of the carrier
status: open
labels: [setoids,relations,tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-03
updated: 2026-11-03
---

A relation `rewrite` through a context `C → D` reads the result's relation
`S` off the evidence rules about `PreservesRelation` that match the context
(`docs/equation-rewrite-design.md` §11.4, from
[[rewrite-setoid-heterogeneous]]). Left out:

- **Hypotheses in scope**: a local `p: PreservesRelation(R, S, f)` names `S`
  only through a rule today; resolution would find it for a known `S`, but
  nothing proposes `S` from it.
- **A fallback to `=`** (`RelId<D>`) when no rule names a relation, as Rocq's
  `Proper` search falls back to `eq`: every function preserves it, and the
  parent then needs evidence over `RelId`.
- **Two changed arguments at different relations**: `Respects2` is over `R`
  alone, so a binary node one of whose arguments left the carrier takes the
  unary route or is refused; the refusal should name both relations.

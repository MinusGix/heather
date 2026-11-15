---
title: More sources for the relation a rewrite carries out of the carrier
status: closed
labels: [setoids,relations,tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-03
updated: 2026-11-07
---

A relation `rewrite` through a context `C → D` reads the result's relation
`S` off the evidence rules about `PreservesRelation` that match the context
(`docs/tactics/equation-rewrite-design.md` §11.4, from
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

## Resolution (2026-11-07)

All three, `docs/tactics/equation-rewrite-design.md` §11.6. Candidates for `S` are
hypotheses in scope (`PreservesRelation(R', S, f)` as written, `f` converting
to the context), then rules, then the rewrite's own `R` when the target is
its carrier, then `RelId<D>` when nothing named one. A change by `RelId`
crosses every context (`preserves_relid`, `preserves_relid_relid`) and chains
into the goal as an `=` step (`trans_relid_l`/`_r`). Two changed last
arguments cross by `Respects2<A, B, D>(RA, RB, S, op)` at the relations they
changed by (`relid_respects2` when both are `=`); elsewhere they are refused
with both relations named. Left: [[rewrite-setoid-sequenced-arguments]].

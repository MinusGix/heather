---
title: Cross two changed arguments one at a time in a relation rewrite
status: open
labels: [setoids,relations,tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-07
updated: 2026-11-07
---

A relation `rewrite` crosses a node by one argument's `PreservesRelation` or
by `Respects2` over its last two (`docs/equation-rewrite-design.md` §9.3,
§11.6). Two changed arguments anywhere else (`k(x, n, x)`, a λ beside an
argument, two children of a constructor) are refused, now naming the
relations each changed by.

Each such node could be crossed one argument at a time, `k(x, n, x) ~
k(y, n, x) ~ k(y, n, y)`, by the unary context of each position and the
result relation's transitivity — `Respects2` is that composite for the last
two. Open questions: which result relation when the two crossings name
different ones (the first that both resolve at, as §11.6's candidates), and
whether to prefer it over `Respects2` when both exist (no: a registered
`Respects2` is one dictionary, the sequence two lookups and a `Transitive`).

Also left from [[rewrite-setoid-heterogeneous-sources]]: a hypothesis whose
type is a telescope ending in `PreservesRelation` (`(u: A) →
PreservesRelation(R, S, f)`) names no relation; only one stated as written
does.

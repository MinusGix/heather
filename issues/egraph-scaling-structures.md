---
title: E-graph structures for large graphs: signature table, union by rank, logarithmic lookup
status: open
labels: [stdlib,performance]
area: tactics
created: 2026-11-02
updated: 2026-11-02
---

The e-graph library's costs are shapes chosen for goal-sized graphs
(`docs/grind-design.md` §5, §8): hash-consing scans the nodes, `find` is a
list lookup, `union` relabels the classes list, and a congruence pass
compares signatures pairwise. A client with hundreds of nodes (a compiler's
value numbering over a large body, e-matching instances) will want a
signature table keyed by class pair, union by rank with the edge forest
kept separately, and nodes in a structure with logarithmic lookup.

Constraint: keep the soundness theorems (`Agrees`, `same_class_sound`)
proved; the guarded congruence merge (`congruent` checked at the graph the
merge is made in) means a faster candidate search needs no new proof.

Not scheduled: wait for a client whose timings show the graph dominating
(`scripts/perf`).

## What it assumes from elsewhere
- **[[egraph-library]]** owns the graph.

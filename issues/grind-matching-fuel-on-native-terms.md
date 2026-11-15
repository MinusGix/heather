---
title: grind: e-matching three lemmas over a native-sized goal runs out of fuel
status: closed
labels: [tactics,performance]
area: tactics
milestone: [tac-general]
created: 2026-11-08
updated: 2026-11-08
---

`grind_using` with three lemmas runs out of the host's per-evaluation fuel
on a goal of ordinary native size. The failure is "evaluating the tactic ran
out of fuel or nesting depth, after 1366 requests". This happens before the
search has a chance to succeed or to report its graph.

Probe (2026-11-08, master `5df757c`): `rt_loop`'s `Fun::post_left` (see
[[grind-unfold-defined-heads]]). The goal's head unfolding is given as a
`refl` local, and the call is
`grind_report(["Valuation::set_here", "Valuation::set_other", "branch_false"], [])`.
The terms involved are a `StructuredRegion` literal
(`branch(x, Ports([Port(rr, 64)]), exhausted, nodes_region([Move(64, rr, o0)]))`),
two nested `Valuation::set`s over a `Valuation::bind`, and their
applications at widths 1 and 64: tens of nodes, not hundreds. Adding three
more `refl` locals ran out after 2064 requests. With every instance written
out and no names, the same graph closes without trouble, so the cost is in
matching and not in closure.

`docs/tactics/grind-design.md` §10 already split each lemma's matching into its own
evaluation (`settled`) for this reason, at 29 nodes. The probe says that is
still not enough at native sizes. The levers, roughly in order:

- find where the fuel goes (matching against a `Valuation` pattern whose
  arguments are λs, near matches asking `Defeq` per node, or the
  pending-premise retries);
- index the graph's applications by head symbol, so that a pattern is
  matched only against nodes whose head it can meet
  ([[egraph-scaling-structures]] owns the structures);
- give the failure the partial graph (the milestone asks that a failure
  hand back its search state, and a fuel failure hands back nothing).

Done when that call either closes or fails with its graph, at the same
fuel, and the matching cost per round is stated as a shape in §5.

## What it assumes from elsewhere
- **[[egraph-scaling-structures]]** owns the e-graph's data structures.
  Assumed here: only that a head-symbol index can sit beside the class
  table.

## Log
- 2026-11-08: Done (docs/tactics/grind-design.md §15.2). The fuel went to linear
  structures (nodes and classes as lists), inlined `let`s recomputed across
  evaluations, whole-graph congruence passes and class tables rebuilt every
  round, and matching through congruent copies. The e-graph's arrays are
  `NatMap` tries (`lib/std/data/nat_map.hthr`), it keeps its class table,
  parents and a signature index and closes incrementally from a dirty list,
  and unlists congruent copies from their class; grind's atoms are keyed,
  pattern roots come from a uses index, and values read across evaluations
  are `shared`. The call closes (with spelling, [[grind-unfold-defined-heads]])
  under the suite's address-space rail. What bounds a run is its total fuel,
  since the arena is not freed during a tactic run (§15.3).

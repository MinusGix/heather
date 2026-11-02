---
title: Prove a hash-consed EGraph::add returns a node of the requested value
status: open
labels: [stdlib,proofs]
area: tactics
created: 2026-11-02
updated: 2026-11-02
---

`EGraph::add` (`lib/std/data/egraph.hthr`) returns an existing node when one
has the same operator and children. `add_agrees` proves the graph stays
sound, but nothing proves the returned node's value is the one requested
(`den(id) = interp(op, kids.map(den))`), which a client with a fixed
denotation needs after a hash-consed add. Today such a client uses `fresh`.

Wanted: `node_among`'s soundness (a found index holds a node whose operator
`eq_op` accepts and whose children are the requested ones) and from it
`EGraph::add_den`.

## What it assumes from elsewhere
- **[[egraph-library]]** owns the graph and its `Agrees` invariant.

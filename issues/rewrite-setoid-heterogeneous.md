---
title: Rewrite along a relation through functions that leave its carrier
status: open
labels: [setoids,relations,tactics,proofs]
area: tactics
milestone: [tac-general]
created: 2026-10-26
updated: 2026-10-26
---

`rewrite(h, e)` along `R` at carrier `C` ([[rewrite-setoid-relations]],
`docs/equation-rewrite-design.md` §9.3) gives every changed node the relation
`R`, so a context that maps `C` elsewhere (`x.abs()` stays in `Rat`, but
`x.floor() : Int`, `size: A → Nat`) is refused: no evidence of either shape
can be stated about it.

Rocq infers a relation per node by `Proper` search with evars: through
`floor` the relation becomes whatever `Proper (Same ==> ?S) floor` resolves
`?S` to (`eq` here), and the parent node must then respect `?S`. Wanted: the
same inference over Heather's evidence vocabulary, `PreservesRelation(RA, RB,
f)` with `RB` found rather than fixed, and the goal's relation composing with
whatever relation reaches its sides (`Trans<D>(…)`).

Design questions this owns: how `RB` is searched (by registered evidence
about `f`, or a designation at `D` such as `≈ at Rat`, falling back to `=`),
and how a mismatch is reported when two arguments of one node arrive at
different relations.

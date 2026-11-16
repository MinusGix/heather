---
title: grind: case splits with the decision tree as the failure, and omega/ring as theories
status: open
labels: [tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

Round 4 of [[grind-port]] (`docs/tactics/grind-design.md` §6): case splits, and
other deciders as theories.

- Split on a `match` scrutinee the graph holds (`split_all`'s `Cases`
  request, `blocker`), closing each branch with the graph extended by the
  branch's equation; the stuck state becomes a decision tree, one graph per
  leaf, which is the object [[parallel-checking-and-caching]]'s rung-2 trace
  format describes.
- Theory combination: equalities between arithmetic terms of one class are
  handed to `omega`/`ring` and equalities they prove come back as edges
  (Nelson-Oppen), each with its proof.

Done when a goal that needs one `Bool` case split and one linear fact closes
by `grind()`, and its failure prints the tree.

## What it assumes from elsewhere
- **[[grind-port]]** owns the graph. Assumed here: only that a graph can be
  extended in a branch and an edge carry any proof.
- **[[tactic-composition-ergonomics]]** owns how deciders compose. Assumed
  here: only that `omega` can be run on a side goal.

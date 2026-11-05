---
title: e-graph: prove e-matching sound against the denotation
status: open
labels: [tactics,proofs]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

The e-graph library's e-matching (`EGraph::ematch`, `lib/std/data/egraph.hthr`,
[[grind-e-matching]]) has no theorem yet. grind does not need one (each
instance is the lemma applied to terms, and the kernel checks the proof),
but a client that acts on matches with no checker after it (a compiler's
rewrite rules over value-numbered code, [[egraph-library]]'s other
customers) wants: every substitution `ematch_at(test, table, p, n)` returns
makes the pattern's denotation equal the node's.

Statement sketch, over the denotation `den` and interpretation `interp` of
the soundness section, given `g.Agrees(den, interp)`:

- a pattern denotation `PatDen(p, σ, i)` (fuel-bounded over the items, a
  variable read through `σ` and `den`);
- `test` sound: `test(q, op, s) = Some(s2)` implies `qinterp(q) = interp(op)`
  on the children and `s2` extends `s`;
- `table` is `g.class_table()` (its members are in their class);
- conclusion: for `s` in `ematch_at(…, n)`, `PatDen(p, s, p.root) = den(n)`.

Completeness (every instance found) is not wanted: grind's report only
lists what was matched.

## Log

- 2026-11-05: gardener: cites a file it shares with [[egraph-add-value-theorem]] (`lib/std/data/egraph.hthr`); [[egraph-setoid-path-algebra]] (`lib/std/data/egraph.hthr`).

---
title: E-graph explanations as setoid evidence: a PathAlg over a relation and its Proper lemmas
status: open
labels: [tactics,stdlib]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-08
---

The e-graph library ([[egraph-library]], `lib/std/data/egraph.hthr`) folds
explanations through any `PathAlg<J, P>`; grind's folds them into `=`
proof terms. A setoid client wants the same path folded into `≈` evidence:
`refl`/`sym`/`trans` of the relation, and a congruence from each operator's
`Proper` (respectful) lemma, found by the operator.

Wanted: a `PathAlg` builder over a relation and a table from operators to
their respect lemmas, used by a `grind` mode at a setoid goal (`a ≈ b` at
`Rat`, `CReal`), where an edge's congruence is only licensed for operators
that respect the relation (a `congruent` that also asks the table).

Soundness: the library's theorem is for `=`; at a setoid the same statement
holds with `≈` in place of `=` and the respect lemmas as hypotheses, and is
worth stating once here rather than per client.

## What it assumes from elsewhere
- **[[egraph-library]]** owns the graph. Assumed here: only `PathAlg` and
  the `eq_op` the closure is given.
- **[[rewrite-setoid-relations]]** owns the `Proper` lemma registry.
  Assumed here: only that a lemma can be found per operator.

## Log

- 2026-11-05: gardener: cites a file it shares with [[egraph-add-value-theorem]] (`lib/std/data/egraph.hthr`); [[egraph-ematch-soundness]] (`lib/std/data/egraph.hthr`).
- 2026-11-08: Stdlib awkwardness survey (docs/stdlib-math-awkwardness-survey.md §3): probed 2026-11-08, `by grind` reads `a ≈ b` at `Rat` as its cross-multiplication equation and cannot close `a.abs() + 1 ≈ c.abs() + 1` from `a ≈ b`, `b ≈ c`. The cheaper half of the ≈ plumbing is [[carrier-respects-as-rewrite-evidence]] (setoid rewrite lacks evidence for every Rat/CReal operation but `+` and `*`).

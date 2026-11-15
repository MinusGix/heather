---
title: One glued evaluator for elaborator, tactics and display: folded forms beside values
status: open
labels: [design,elaboration,performance,tactics]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Item 3, part 2, of the fundamental-improvements memo of 2026-10-31 (Claude Doc, https://claude.ai/artifact/Y2Jo9y9Mgd52QdguvaL43s): the elaborator, the tactics and the display share
one evaluator that keeps each term's as-written (folded) form beside its
computed value, as smalltt does.

The kernel already has glued neutrals (`docs/kernel/nbe-conversion-design.md` §5).
The elaborator's own whnf is the recurring cost and respelling source
([[elab-whnf-copies-straight-continuations]], [[elaborator-canonical-type-spelling]],
the "elaborator whnf is the cost" finding on computed types). Tactics compare
atoms syntactically: in the sequencing design's probe P2, `omega` treated
`count_words(xs)` and its unfolded `foldl(…).words` as two atoms, although
`refl` proves them equal.

## Scope

- Establish how much of glued evaluation the elaborator already has, and
  where it converts on terms instead of values.
- Conversion uses values. Display, metavariable solutions and tactic atoms
  use the folded form.
- Tactic atoms compare up to a declared transparency (Lean's reducibility),
  with opt-in interface definitions ([[proof-modularity-design]]) opaque.

## Done when

A design note decided by Minus, with the first slice filed. The note states
which open spelling issues it retires.

## Log

- 2026-11-05: gardener: cites a file it shares with [[elab-emits-normal-form-of-matched-type-argument]] (`docs/kernel/nbe-conversion-design.md`).

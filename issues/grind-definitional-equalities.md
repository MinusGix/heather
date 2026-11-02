---
title: grind: terms equal by definition alone stay in different classes
status: open
labels: [tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

grind compares atoms by `Defeq` but applications only by structure, so two
terms equal by definition alone sit in different classes. Found by
[[grind-library-sweep]] in `Int::neg_add`'s induction step:

- the goal says `-(a + OfNat(Succ(k)))`, the lemma `Int::add_isucc` speaks
  of `a + b.isucc()`, and `OfNat(Succ(k))` is `OfNat(k).isucc()` only by
  computation, so the pattern never matches;
- with that step made syntactic, the graph still stops one equation short:
  `-a + -OfNat(k)` (from the induction hypothesis) and
  `(-a + Int::negOfNat(k)).ipred()`'s operand differ by `-OfNat(k) ≡
  Int::negOfNat(k)`.

The hand proofs cross these by `refl`-typed `cong` steps the kernel accepts
up to conversion. Options, cheapest first:

1. When matching a pattern's application against a node fails on the
   operator, ask `Defeq` of the instance before giving up, for patterns a
   lemma marks (or for constructor-headed ones: `OfNat(Succ(k))` against
   `isucc(…)`), bounded per round.
2. After a round with no new instance, compare pairs of nodes of the same
   type whose heads are definitions that unfold (`neg`, `negOfNat`) by
   `Defeq`, and merge with a `refl` justification (the kernel checks it).
   Quadratic in such nodes; the stuck report already names the candidate
   classes.
3. Normalise terms to a canonical head form on reading (`whnf` at reducible
   transparency), Lean's choice; needs a transparency notion Heather does
   not have.

Done when `neg_add`'s `Succ` step closes by `grind_using` with the four
lemmas its `calc` cites.

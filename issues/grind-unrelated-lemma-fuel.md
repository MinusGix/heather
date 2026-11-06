---
title: Keep grind's proofs closing when a commutative lemma is added beside their hints
status: open
labels: [tactics, grind, robustness]
area: tactics
milestone: [tac-general]
created: 2026-11-06
updated: 2026-11-06
---

A grind call that closes can stop closing when one more lemma is named,
even one its proof does not need. `neg_add_succ`
(`lib/_tests/std/tactic/grind_tests.hthr`) closes from its four lemmas;
with `Int::add_comm` among them it runs out of evaluation fuel:

```heather
theorem neg_add_succ_unrelated(a: Int, k: Nat, ih: -(a + OfNat(k)) = -a + -OfNat(k)): -(a + OfNat(Succ(k))) = -a + NegSucc(k) {
    by grind_using(["Int::add_isucc", "Int::add_comm", "Int::neg_isucc", "Int::add_ipred", "Int::ipred_negOfNat"], [])
}
// error: `by grind_using(…)`: evaluating the tactic ran out of fuel or nesting depth, after 2699 requests
```

Same result and request count on master e4f0cf6 and with
[[grind-report-lurking-hints]]'s provenance, so it is not that change.

Found by the robustness check of Gopinathan et al. (CAV 2025, Axolocl, RQ2):
a proof that survives reordering and an unrelated addition is one a growing
library will not break. The other mutations tried all close: `tower_nil`
and `regroup` with their lemmas reversed, `regroup` with two list lemmas
added, `tower_lens` with `Int::add_comm` and `List::append_nil` added,
`neg_add_succ` with its four reversed
(`lib/_tests/std/tactic/grind_mutation_tests.hthr`).

Why it matters: the hint interface (docs/grind-design.md §9.4, §9.6;
[[lemma-selection-and-search]]) expects callers, people or models, to
over-supply hints and narrow afterwards. Over-supply that exhausts fuel
before the narrowing step defeats that.

First suspects, measured before changing anything: which evaluation runs
out (a round's matching, `close_passes`, or a near match's `Defeq`
candidates; §13.1 notes candidates are every whole term in order, with no
key on head or type), and whether `add_comm`'s instances, added both ways
every round, grow the graph past what one `settled` piece holds.

## Done when

The probe above closes, or fails with grind's own "stopped after N rounds"
report rather than the evaluator's fuel error, and it joins
`grind_mutation_tests`.

## What it assumes from elsewhere

- **[[grind-scope-size-cost]]** owns a call's cost growing with imports.
  Assumed here: nothing; this is growth with the hint list, measured apart.

---
title: Keep grind's proofs closing when a commutative lemma is added beside their hints
status: closed
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

Why it matters: the hint interface (docs/tactics/grind-design.md §9.4, §9.6;
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

## Log

- 2026-11-06: Done, and the cause was not grind's. The failure is the
  evaluator's native-depth rail, not fuel (the run's largest force used a
  sixth of its fuel; at a 1000× fuel budget it failed the same way at the
  same request). The sides do meet after the extra rounds; the run dies
  reading the result. Any tactic that answers more than about 2,000
  requests under a `bind` did: `spin(2200).bind(λ e => pure(e))` failed and
  `spin(1900)` passed. `add_comm` only pushed grind past that (2,699
  requests; `grind_run` wraps `saturate` in `.bind(λ p => pure(lams(…)))`).
  Mechanism: a tier-2 `match` reads a function child through the alias
  `k := λy. ⟨f' y, c y⟩`, so the proof of an inner run's `n`-th tree is the
  `(n-1)`-th's applied, a chain the host's `pin` never touches (it pins the
  outermost tree only, [[tactic-run-continuation-chain]]), forced whole by the
  final `Pure`'s `J`: 2,047 nested `app@(x2; x0)` re-entries. Fixed in the
  evaluator: an elimination whose head is a variable bound to a closure waits
  on the heap frame stack (`Eval::await_bound`) instead of re-entering
  `drive`, docs/kernel/native-depth-budget-design.md §9. The probe closes and joined
  `grind_mutation_tests`; `long_runs` (crates/elab/tests/tactic_host.rs) runs
  3,000 requests under a bind; `a_chain_through_variable_heads_needs_no_native_depth`
  (eval_differential.rs) pins the kernel side. Found with temporary request,
  force-depth and drive-stack tracing in the host and evaluator (not kept).

---
title: Invariant rules for loops and contracts for procedures, so imperative code is proved by rules
status: open
labels: [proofs,elaboration,native]
area: language
milestone: [lang-proof-modularity]
created: 2026-10-31
updated: 2026-11-14
---

Round P4 of `docs/compiler-milestones-proposal.md` (§6.2, §7): proofs about imperative code through rules,
not unfolding.

## Scope

- An invariant rule generated beside each loop from [[pure-imperative-statements]]: `inv(init)` and `inv(s) → inv(step(s, x))` give `inv(result)`.
- Contracts of compiled procedures cited at call sites, after [[native-compiled-procedures]] (the contract shape is [[native-procedure-contracts]]).
- A property of a tool rewritten as a `runtime fn` ([[effects-uniqueness-surface]]) proved about its Heather function, not its `Source`.

## Done when

`count_words`'s spec is proved with an invariant and a step lemma in a few lines, and one property of a rewritten tool is proved about its function.

## Log

- 2026-10-31: 2026-10-31: docs/sequencing-surface-design.md §7.2 proposes that the invariant rule be library theorems over the two lowered shapes (List::foldl_invariant, List::for_in_invariant) plus a tactic step that applies them, not a per-loop generator, because every lowered for is foldl or for_in applied to a named step. Pending Minus's decision (§11 item 5).
- 2026-11-14: a step of a `decreases` loop at its `if h:` test is now `trans(f_unfold(x), Bool::taken_true(c, e))`, the arms learned from the unfolding ([[unify-through-match-arms]]); the hand induction over the count remains this issue's.

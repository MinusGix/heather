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
- 2026-11-14: The `decreases` half, for loops counting a word (the native work's loops, `/mnt/project-files/design/language-feature-threads-2026-11-14.md` §2). Generated `f::step`/`f::done` beside `f_unfold` (now also `f::unfold`) for a body that is one test with an equation (`docs/decreases-unfolding-design.md` §6.1), over `Bool::convoy_true`/`convoy_false` and `decide_bit_of` in `bool.hthr`; the rule `BitVec::loop_up` and `BitVec::run_up_invariant` in `lib/std/bitvec/bitvec_loop.hthr`. `Sha256::begin` is one call to the rule, and `Sha256::expand`'s invariant (the whole schedule follows §6.2.2 from the first sixteen words) is proved through it (`lib/_tests/native/crypto/sha256_schedule_tests.hthr`). Left: the `for` half (`List::foldl_invariant`, `List::for_in_invariant` and the tactic step of §7.2), `count_words`, procedure contracts, and a tactic step that supplies `g` from `f::step` so a client gives only the invariant.
- 2026-11-14: a step of a `decreases` loop at its `if h:` test is now `trans(f_unfold(x), Bool::taken_true(c, e))`, the arms learned from the unfolding ([[unify-through-match-arms]]); the hand induction over the count remains this issue's.

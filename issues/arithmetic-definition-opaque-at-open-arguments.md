---
title: A one-line arithmetic definition: opaque to omega at open arguments, and out of fuel against its unfolding
status: open
labels: [tactics,omega,kernel]
area: tactics
created: 2026-11-24
updated: 2026-11-24
---

Found proving the word map's specification ([[runtime-hash-map-spec]]).
Three ways a one-line definition cost more than its body, all met while
naming the distance between two slots of a table, `(b + 4 - a) % 4`:

1. **`omega` holds `WordMap::dist(a, b)` at open arguments as an atom.** Its
   body is linear arithmetic with a literal modulus, which `omega` reads
   when written out; behind the name it found a model with
   `dist(j, s) = 0` and stopped. docs/proof-patterns.md §3 says `omega`
   "follows a definition to its arithmetic", which held only for closed
   arguments here. The proofs write the distance out everywhere.
2. **The kernel runs out of fuel comparing a defined proposition with its
   unfolding.** `fn WordMap::Before(k, t, s) → Type { ((t + 4 - h(k)) % 4)
   < ((s + 4 - h(k)) % 4) }`, passed a proof of the unfolded inequality,
   was refused "OutOfFuel … differs at `(t + 4 - toNat(word_map_home(k))) %
   4 < …` against `Before(k, t, found.witness)`": the kernel reduced the
   inequality's side (`Nat::Lt` over `%`) instead of δ-unfolding `Before`.
   The record field was rewritten with the inequality inline.
3. **`refl` between a `runtime fn` and its body runs out of fuel.**
   `WordMap::insert(m, k, v) = WordMap::insert_at(m, k, v, word_map_home(k),
   4)` (the body is `let r = insert_at(…); Mutated(r.after, r.value)`) is
   refused "OutOfFuel": the kernel unfolds the measured probe at its literal
   budget `4` rather than η-expanding the neutral record. η stated once at a
   neutral `r: Mutated<WordMap, u64>` and instantiated converts at once
   (`WordMap::mutated_eta`, `insert_is`, `remove_is`).

## Wanted

`omega` opens a non-recursive definition whose body is arithmetic at open
arguments too; the kernel's lazy δ prefers unfolding a definition whose
body is the other side's head (`Before` against `Nat::Lt`), and prefers
record η to unfolding a measured recursion at a literal.

## Log

- 2026-11-24: Item 1 fixed (branch `claude/proof-tooling-omega`; items 2 and 3, the kernel's δ heuristics, belong to the other proof-tooling thread). `omega` reads a call at open arguments as its body when a few head reducts (the δ step and the β steps instantiating its parameters, `Unfold::OpenArithmetic`) reach `+`, `*`, `div`, `mod` or a successor whose leaves spell; the subtraction split looks through the same opening, so `dist(a, b) = (b + 4 - a) % 4` is its body, split and all. A recursive definition stays an atom (stuck on its `match`). `word_map_laws.hthr` now defines `WordMap::dist` and states its distance lemmas with it; their callers' written-out facts convert. Design §26; probes and controls in `lib/_tests/std/tactic/omega_tests.hthr` ("Definitions at open arguments").
- 2026-11-24: 2026-11-24 (items 2 and 3; item 1 is the omega thread's):

  Item 3 fixed (2d35946). In `Conv::tm_w`, a δ-stuck side against a side
  with no defined head was unfolded transparently before the type-directed
  Σ-η arm saw either; against a pair at a Σ (`Mutated(r.after, r.value)`)
  that ran `insert_at`'s measured recursion at its literal 4.
  `Conv::eta_before_unfolding` now tries Σ-η there first, under
  `delta_lazy`'s guard, only where the type's view is a Σ (a `Vec` keeps its
  own arm), so `fst(insert_at(…))` meets the pair's `r.after` at the same
  spine. `WordMap::insert_is`/`remove_is` are `refl` and
  `WordMap::mutated_eta` is gone. Probe:
  lib/_tests/native/runtime/word_map_tests.hthr, with a negative control
  (a wrong second field, refused by the kernel).

  Item 2 does not reproduce on this tree: `Before(k, t, found.witness)`
  against a proof of the unfolded inequality, directly and through a second
  definition (`home(k)`, as the original spelled it), converts at once by
  the newer-head rule (`Before` unfolds to `Nat::Lt`, then the spines meet);
  the reversed proof is refused promptly as a mismatch (same probe). The
  original refusal quoted a *difference* ("differs at …"), so it was most
  likely a wrong proof whose refutation went to the kernel, where deciding
  non-convertibility unfolds `%` at open arguments; no heuristic change made.
  Left open for item 1.
- 2026-11-24: 2026-11-24: Item 3, narrowed after the whole-library gate (65ab503, 5de6efe): tried against every pair, the η attempt exhausted the budget in laid-record accessor checks (runtime_held_array_tests' Sums::nudge, Sha256::run, Sha256::close). It now runs only where a component of the pair, down its right-nested Σ, is stuck at the other side's head (directly or past newer heads, a record's projection), and on a fixed allowance (ETA_FUEL, 4096 steps, nested attempts included) whose exhaustion is not a verdict. Kernel lanes and the library gate are green with both.

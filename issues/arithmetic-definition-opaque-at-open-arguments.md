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

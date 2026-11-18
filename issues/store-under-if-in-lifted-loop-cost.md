---
title: A store under an `if` in a lifted loop makes the loop's check an order of magnitude slower
status: open
labels: [performance,elaborator,loops]
area: language
created: 2026-11-17
updated: 2026-11-17
---

A loop over a span whose body stores into the receiver under an `if` checks, but far more slowly than the same loop with the store unconditional (docs/language/sequencing-surface-design.md §23.6). Programs over spans (binary search, the UTF-8 validator, a running maximum) are mostly loops with `if`s in them, so this is in the way of the end-to-end demos.

## Measured

2026-11-17, release binary, `--cache --timings`, one module holding only `Bytes(n)` and the functions below:

- A running maximum, `for i in 0..s.len() { for j in 0..i { if s[i] < s[j] { s[i] := s[j]; } } }`: 39 s, of which the elaborator's `whnf` is 17 s.
- The same with the inner loop a `while j < i invariant i < s.len()`: 68 s.
- The same nested `for`s with the `if` removed (`s[i] := s[j];`): 3.2 s.

The cost is not the facts a loop is given (§23.5): the `while` variant states its invariant and is slower still.

## Next

Find where the `whnf` time goes (`--timings` per declaration of the family: `#body`, `#ext`, `_unfold`, `#keeps`, `#found_N`). A guess to check first: the statement `if` at the receiver is a match whose two arms each end in the receiver, and every copy of the body the companions make carries both arms, with each arm's reads searching for their found proofs again ([[squashed-found-proof-searched-per-copy]]).

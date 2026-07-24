---
title: Choose the effects story (uniqueness threading vs interaction trees)
status: open
labels: [design, effects]
created: 2026-07-22
updated: 2026-07-24
---

Effectful runtime functions never run at kerneltime, so the question is what
kerneltime object they *denote* so theorems about them are stateable. Split
the programming surface from the reasoning denotation; users never write
monadic types.

Current leaning — the two candidate denotations compose, staged:

1. **Uniqueness typing (Clean-style) first.** `&uniq Fd` is a capability;
   `Fd::read : uniq Fd -> (uniq Fd, [u8; N])`. Effectful code is literally
   pure, `equiv` stays plain equality, and uniqueness is an *intensional
   library discipline* over boxed code (like the lifetime-system idea), not
   kernel machinery. This is also the first serious test of the
   "disciplines are libraries" bet.
2. **Interaction trees later**, when concurrency or genuine external
   nondeterminism forces trace-shaped semantics for specific primitives.
   Cost: coinduction in the kernel and bisimulation replacing propositional
   equality — check against the Coq DeLaM formalization whether layering
   tolerates it, or whether some weaker finitary notion suffices.

Avoid: a user-visible CPS/monadic elaboration target that people read and
prove against directly (monad-shaped goals + esoteric types, no equational
payoff).

Related: [[ir-simulate-design]] (trace-shaped simulate), [[kernel-v0-scope]]
(coinduction explicitly out of v0).

## Log

- 2026-07-24: CONSTRAINT from the equality-notation decision ([[surface-syntax]], 2026-07-24): `=` is now propositional equality (and `let` binding). Any future imperative/assignment-like effect syntax must therefore NOT use bare `=` (`place = value` would be indistinguishable from asserting `place = value`, since only `let` disambiguates). Use `:=` (user's stylistic lean) or `<-`. Applies whichever way the effects story lands (interaction trees are the plan to explore); mutable-value ergonomics are wanted, so pin the assignment glyph early.

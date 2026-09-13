---
title: The transducer memo is keyed on closure syntax, so a negative verdict is re-derived at every call site with a different environment
status: open
labels: [kernel,evaluator,performance,bitvec]
created: 2026-09-13
updated: 2026-09-13
---

Filed from K1 round 3 (2026-09-13). `ValueArena::transducers` is keyed on `(step.ident(), motive.ident())` — body pointer plus environment identity — so the same width fold reached from a different call site (a different environment) is a different key and re-probes: a motive walk plus, for a step that gets as far as the table, one application per combination. On the reused_callee certificate ~17 600 of ~22 200 probes were negative and repeated per occurrence. The seconds were flat overall, and the coordinator's review added a syntactic gate (a motive written `Nat` skips the memo) and the pointer hasher, which keep the lookup off the ordinary `Nat` folds — but a negative verdict on a genuine width fold is still re-derived per occurrence.

The fix is a memo the verdict is actually a function of: the class depends on the step's and motive's *syntax* and on what the environment binds at the free variables the probe touches, not on the environment's identity. Options: key on syntax plus the values of the free variables the motive and step mention (a small vector of closure identities), or memoize the negative verdict on syntax alone when the probe's failure did not consult the environment (a stuck case on a probe variable, a non-`Vec` domain). Completeness-only: the verdict is the same either way. Measure on the certificate's probe counts (the round's `--timings` and value-metrics runs) before choosing.

Related: [[kernel-native-bitvector-values]], [[nat-run-algebra-primitives]] (the `Nat` classes' memo has the same key shape, by closure address).

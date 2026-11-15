---
title: Split the small-step reducer's step frame so it can share the native depth bound
status: open
labels: [kernel,reducer]
area: kernel
created: 2026-10-26
updated: 2026-10-26
---

Filed out of [[eval-native-frame-size]], which split the evaluator's and conversion's dispatchers and doubled `NATIVE_DEPTH_LIMIT` to 2048, but left the reducer alone.

`reduce::step_term_frame` is one `match` over every rule, with the congruence recursion (`step_scrut`, `step_term_in`) inside the arms, so a counted reducer level stands on the union of every rule's locals: about 3.7 KB in release on the frame alone, several times a counted evaluator level. It therefore keeps the old bound, as `REDUCER_DEPTH_LIMIT = 1024` (`crates/kernel/src/reduce.rs`).

The shape that worked elsewhere (docs/kernel/native-depth-budget-design.md §8): make the recursive step a small frame. Concretely, `step_term_frame` could return either a finished step or "blocked at this sub-term", leaving the recursion to `step_term_in`'s small frame and the rebuild of the blocked position to an out-of-line function. Then `REDUCER_DEPTH_LIMIT` can be retired in favour of the shared bound.

Not urgent: the reducer spells and is the oracle's; the checking path's depth is the machine's and conversion's. It matters when a diagnostic or the syntactic conversion domain meets a deep blocked spine (the `x < pow(3, 5000)` case of design §7).

## What it assumes from elsewhere

- **[[eval-native-frame-size]]** owns the measurements and the rule; assumed here only that the reducer frame is the one counted frame it did not split.

## Log

- 2026-11-05: gardener: cites a file it shares with [[conversion-typed-eliminator-congruence]] (`crates/kernel/src/reduce.rs`); [[kernel-psi-bound-cache]] (`crates/kernel/src/reduce.rs`).

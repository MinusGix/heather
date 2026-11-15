---
title: Course-of-values convoy may mis-index a motive mentioning a second ambient variable
status: closed
labels: [elaboration,recursion,proofs,robustness]
area: language
created: 2026-09-18
updated: 2026-11-08
---

An accumulator note, **unverified** — a hypothesis from the implementer of
[[list-course-of-values-recursion]], recorded so it is read before it is
rediscovered.

Both convoy routes — `chain_convoy` for `Nat` (`matching/routes.rs`) and
`wf_chain_convoy` for chain-shaped `Wf` inductives (`wf.rs`) — reindex the
recursion's motive at a nested `match`'s scrutinee by the same shape, and
that shape is believed correct only because a *synthesized* motive mentions
the scrutinee `z` and nothing else ambient. A motive that also mentions a
second ambient variable (a parameter the recursion generalizes over, say)
would be mis-indexed by both routes identically.

To settle: write a depth-2 recursion whose motive mentions a second
generalized variable (`docs/tactics/ih-generalization-design.md`) at a dependent
motive, on `Nat` and on `List`; it either checks or produces a kernel
refusal at the convoyed arm. If it refuses, the fix is in the reindexing
(carry the motive's full context, which `GuardKind::{Nat, Wf}` already
store as `gamma`), not in the callers.

## Log

- 2026-11-08: 2026-11-08: CONFIRMED and FIXED, and wider than hypothesized. Any variable of the recursion's own context was mis-indexed, not only a generalized one: a type parameter (`theorem skip_all<A>(xs: List<A>): Skip(xs)`, `LevelMismatch`) or a parameter before the decreasing one (`keep_all(k, xs)`, `every2(k, n)`, `NotConvertible`) made the kernel refuse a depth-2 recursion on both `Nat` and `List`. A generalized parameter after the decreasing one was fine, being a `Π` of the motive and not a free variable, which is why nothing in the library met it. Cause: both convoys reindexed the motive (and `List`'s `tail_D`), which is scoped over the recursion `match`'s context plus z, past the binders since the *guard* (`by`) instead of those since the *`match`* (the arm's branch binders included); a motive reading only z cannot tell the difference. Fix: reindex by `cx.gamma` minus the stored `gamma`, in `chain_convoy` (`matching/routes.rs`) and `wf_chain_convoy` (`wf.rs`). Probes in `lib/_tests/std/core/recursion_window_tests.hthr`, each refused on master.

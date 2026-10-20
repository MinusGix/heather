---
title: Course-of-values convoy may mis-index a motive mentioning a second ambient variable
status: open
labels: [elaboration,recursion,proofs,robustness]
area: language
created: 2026-09-18
updated: 2026-09-18
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
generalized variable (`docs/ih-generalization-design.md`) at a dependent
motive, on `Nat` and on `List`; it either checks or produces a kernel
refusal at the convoyed arm. If it refuses, the fix is in the reindexing
(carry the motive's full context, which `GuardKind::{Nat, Wf}` already
store as `gamma`), not in the callers.

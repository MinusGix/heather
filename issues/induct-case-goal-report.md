---
title: induct: a hole under all_goals is an internal error, and a case's report repeats locals and prints a kernel case
status: open
thread: Make compiler correctness proofs elegant
labels: [tactics,diagnostics,bug]
area: tactics
created: 2026-11-16
updated: 2026-11-16
---

Found probing `induct` on a compiler-shaped function (`/mnt/project-files/compile-proofs/`, 2026-11-16). Three things in what a case shows, one of them a crash.

1. **`induct f(x̄); all_goals { ? }` is an internal error**: "internal: a hole was re-elaborated in a different context". The arms form (`Seq => ?`) reports the goals. The speculative run of the block on each IH premise is the likely cause. A hole under `all_goals` should report every case's goal: it is how a proof by `induct` is started.
2. **A case lists its locals twice.** The `Seq` case shows `p`, `names`, `c`, `e` and `ih` each two times (the theorem's and the case's), and the first `ih` at a type whose binder is the Σ encoding of `Out` (`(x: «Σ[0,0](«sEq»[0](«Nat»; 4129290884; …`). Only the case's own should be listed.
3. **A stuck match on a call's result prints as the kernel's `case`.** `eq : emits(Seq(first, rest), p, names) = case[0,0,0](M El[0](app@(u@538^{·}; …` where the source has `match first.emits(p, names) { None => None, Some(c) => … }`. [[lowered-match-printing]] (closed) prints the lowered forms of a written match; this one comes from the function's unfolding.

Also seen: `split_all` lists the hypothesis it leaves (`__split_all_x7`) twice.

## Done when

The three are probes in `lib/_tests/std/tactic/induct_tests.hthr` (an `// expect-error:` hole under `all_goals` that names each case), and the goal report for the model's `Seq` case shows each local once, with `eq`'s right side as the source's match.

## Log

- 2026-11-16: Item 2 and the `split_all` note done: the goal listing
  (`Goals::reports`, `crates/elab/src/goals.rs`) leaves out a binder or
  alias that a later one of the same name shadows, so a re-bound local shows
  once, at its re-bound type (`goal_holes.rs`
  `a_shadowed_local_is_listed_once`). Items 1 and 3 stay open.

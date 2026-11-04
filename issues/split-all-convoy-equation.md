---
title: split_all builds a term the kernel rejects at a `match h:` whose arm uses its equation
status: closed
labels: [tactics,elaboration,soundness-gap]
area: tactics
created: 2026-10-26
updated: 2026-10-26
---

Found proving a measured loop's pass for
[[function-ir-loop-measure-recursion]]. `match h: c { … }` elaborates to a
convoy: a match on `c` whose motive is `λ z => (c = z) → T`, applied to
`refl`. `split_all` abstracted every occurrence of `c` in the goal as the
split's `z`, the convoy's motive and `refl` included, so in each case the
convoy's arm was handed an equation about the constructor, not about `c`.
An arm that uses its equation (an obligation `pred_lt(n, h)` inside a
recursion's bound) was then ill-typed, and the kernel refused the
declaration (`NotConvertible`) after the elaborator accepted it. Nothing
unsound was admitted; the proof just could not be written with `split_all`.

A second gap showed at the same goals: a step that answers in some arms and
recurs in others, proved by `all_goals { hg }` with `hg` stating the
recursions, met its answer leaves as `acc = acc`, which `hg` does not
prove.

## Log

- 2026-10-26: Fixed. The split abstracts a convoy on its scrutinee as a
  convoy on `z` that keeps its motive, arms and `refl` at `c`
  (`goal_combinators::abstract_scrutinee`), and when one is in the goal the
  split's motive takes the case's equation `q : c = z` as a second binder,
  each such convoy applied to `q` (`dependent_motive`); the split is
  elaborated with that motive (`elab_convoy_dependent`), so in each case the
  convoy takes its arm with the case's equation. The search looks through a
  convoy to its match (`head_match`), and a co-occurrence reached through a
  definition is read at the reduct its arguments are all substituted into,
  not part-way through its β-steps, where the convoy is under a binder and
  cannot be moved apart from its `refl`. A goal whose sides the split made
  one term is closed by `refl` (`Step::Closed`), as a refuted case is closed
  by `absurd`. Tests: `goal_combinators.rs`
  `splits_a_convoy_whose_arm_uses_its_equation` and its negative control.

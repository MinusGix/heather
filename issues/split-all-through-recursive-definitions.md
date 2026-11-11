---
title: split_all: unfold a recursive definition with its recursive calls respelled
status: open
labels: [tactics,elaboration,proofs]
area: tactics
created: 2026-10-01
updated: 2026-11-11
---

`split_all` finds the matches blocking a goal by unfolding transparent
definitions (`docs/goal-combinators.md`). When the definition is structurally
recursive, its unfolding is the kernel's recursor: after the split,
`wc_l(Cons(byte, rest))` becomes a raw eliminator applied to `rest`, not
`wc_l(rest)`. A leaf such as `omega` cannot spell that ("could not spell a
natural expression"), and even if it could, the atom would not match the
induction hypothesis's `wc_l(rest)`.

This blocks the routine half of every fold proof. `wc_l.hthr`'s
`count_lines_fold` and `wc.hthr`'s `wc_lines_cons` are still hand-written
motives for exactly this reason.

What is needed is equation-style unfolding: one step of a recursive function
at a constructor argument, with the recursive calls spelled as calls of the
function. That could be the elaborator's own (a refold after ι), or an
equation lemma the declaration publishes and the splitter rewrites with.
Either way the result has to convert with the raw reduct, so the kernel
gate is unchanged.

Acceptance: `count_lines_fold`'s Cons case is
`{ let same = …; let more = …; split_all; all_goals { omega } }`.

## Log

- 2026-11-05: gardener: cites a file it shares with [[split-all-revise-hypotheses]] (`docs/goal-combinators.md`); [[tactic-composition-ergonomics]] (`docs/goal-combinators.md`).
- 2026-11-11: The equation-style unfolding exists for `simp_only`: `goal_combinators::recursion_at_constructor` takes the reduct walk's refolded firing (`refold.rs`) to the selected arm, contracts the hypothesis's β-redexes and child reads, and replaces each child by the pattern variable that converts with it, so `simp(Seq(a, b))` reads `seq(simp(a), simp(b))`. `simplify_goal_with(…, recursive: true)` turns it on; `split_all` still calls `simplify_goal` without it, since turning it on there changes the goals library proofs were written against (whole-library re-elaboration). That switch is what is left of this issue.

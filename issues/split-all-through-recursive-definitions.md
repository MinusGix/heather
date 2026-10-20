---
title: split_all: unfold a recursive definition with its recursive calls respelled
status: open
labels: [tactics,elaboration,proofs]
area: tactics
created: 2026-10-01
updated: 2026-10-01
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

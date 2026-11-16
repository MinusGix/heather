---
title: split_all: reduce a non-recursive definition at the constructor a split substituted
status: closed
labels: [tactics,proofs,elaboration]
created: 2026-10-02
updated: 2026-10-02
---

After `split_all` splits a scrutinee, it simplifies through constructors,
projections and β (docs/automatic-author-surface-design.md@4acf2fe §2.1), but not
through a *non-recursive* definition applied to the constructor it just
substituted. The goal keeps the definition's head, so a leaf such as `omega`
sees a stuck spelling. Two cases from the 2026-10-02 probes
(docs/archive/native-programs-read-like-programs-design.md §4):

- **Bool connectives.** A step whose predicate is
  `!b.unsigned_lt_bit(10) && b.unsigned_lt_bit(11)`: the Filter's `advances`
  default fails with "Omega could not spell a natural expression". After the
  comparison is split, `Bool::and(Bool::not(True), …)` is not reduced, so the
  step's match stays stuck. Every predicate written with `&&`, `||` or `!`
  hits this.
- **Helpers at a constructor.** `words(split_at(False, x, pieces))`, where
  `split_at` is a match on its first argument, stays as written, and omega
  takes it as an atom distinct from `words(onto_first(x, pieces))`. The
  generic run-count lemma had to be written with explicit motives instead.

Fix: after substitution, δι-reduce a transparent non-recursive head whose
matched argument is now a constructor, then simplify again. The recursive
case is [[split-all-through-recursive-definitions]] (refolding needed). This
case needs none, because the reduct contains no recursor.

Related: [[native-programs-read-like-programs]].

## Log

- 2026-10-02: Fixed 2026-10-02 (S6 of native-programs-read-like-programs; docs/archive/native-programs-read-like-programs-design.md S6, docs/tactics/goal-combinators.md). Suite 3156 passed.

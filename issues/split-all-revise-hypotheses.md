---
title: split_all: revise hypotheses that mention the scrutinee it splits
status: open
labels: [tactics,proofs,elaboration]
area: tactics
created: 2026-10-02
updated: 2026-10-02
---

When `split_all` splits a scrutinee, the motive covers only the goal. A
hypothesis already in context that mentions the scrutinee keeps its old type
in every branch, so a leaf sees `ih: … runs_start(cut, inside) …` beside a
goal where `cut` is `False`. Found on 2026-10-02, in the run-count case lemma
(docs/native-programs-read-like-programs-design.md §4.1).

The workaround is to state the premise as a binder of the goal, `(cut,
inside: Bool) → (premise) → conclusion`. Then the Bool binders are split as
they are introduced, and the premise is introduced afterwards at its
simplified type (S6, docs/goal-combinators.md).

Wanted: revert the hypotheses whose types mention the scrutinee into the
motive, as Lean's `cases` does. Each arm then re-introduces them at the
specialized type, simplified. A premise can then be written as an ordinary
parameter.

Related: [[split-all-reduce-defined-heads]].

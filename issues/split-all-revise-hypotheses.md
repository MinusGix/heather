---
title: split_all: revise hypotheses that mention the scrutinee it splits
status: open
labels: [tactics,proofs,elaboration]
area: tactics
created: 2026-10-02
updated: 2026-10-31
---

When `split_all` splits a scrutinee, the motive covers only the goal. A
hypothesis already in context that mentions the scrutinee keeps its old type
in every branch, so a leaf sees `ih: … runs_start(cut, inside) …` beside a
goal where `cut` is `False`. Found on 2026-10-02, in the run-count case lemma
(docs/archive/native-programs-read-like-programs-design.md §4.1).

The workaround is to state the premise as a binder of the goal, `(cut,
inside: Bool) → (premise) → conclusion`. Then the Bool binders are split as
they are introduced, and the premise is introduced afterwards at its
simplified type (S6, docs/tactics/goal-combinators.md).

Wanted: revert the hypotheses whose types mention the scrutinee into the
motive, as Lean's `cases` does. Each arm then re-introduces them at the
specialized type, simplified. A premise can then be written as an ordinary
parameter.

Related: [[split-all-reduce-defined-heads]].

## Log

- 2026-10-31: 2026-10-31: slice 2 of dependent-match-compiler refines hypotheses at a computed scrutinee in the elaborator's motive-less match, but split_all's Cases (host.rs cases_request) builds its own motive from the goal alone, so this stays open. The fix is to generalize the about-the-scrutinee locals there the way refined_by_occurrence selects them, every one (a tactic leaf may read any).
- 2026-11-05: gardener: cites a file it shares with [[literal-classes-need-importing]] (`docs/archive/native-programs-read-like-programs-design.md`); [[split-all-through-recursive-definitions]] (`docs/tactics/goal-combinators.md`); [[tactic-composition-ergonomics]] (`docs/tactics/goal-combinators.md`).

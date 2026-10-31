---
title: A match on a computed scrutinee refines the hypotheses that mention it
status: open
labels: [elaboration,match,motives,proofs]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Slice 2 of [[dependent-match-compiler]] (docs/dependent-match-compiler-design.md §5).

`Elaborator::refined_hypotheses` (crates/elab/src/generalize.rs) generalizes later binders only when the scrutinee is a local variable. Extend it to a computed scrutinee: a binder whose type contains the scrutinee term (`==`) is generalized, with its type abstracted to `T[z/e]`, under the same selection rule (an arm names it or the goal mentions it, plus its dependencies).

## Done when
- Probe P1 (`comp_hyp`, design §12.1) checks: in the `False` arm `h` is `False = True`.
- Checked here, and closed if so: [[split-all-revise-hypotheses]], the first half of [[cov-window-in-theorem-arms]], [[nested-match-on-list-tail-motive]].

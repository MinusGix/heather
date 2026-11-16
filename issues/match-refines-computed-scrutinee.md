---
title: A match on a computed scrutinee refines the hypotheses that mention it
status: closed
labels: [elaboration,match,motives,proofs]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Slice 2 of [[dependent-match-compiler]] (docs/language/matching/dependent-match-compiler-design.md §5).

`Elaborator::refined_hypotheses` (crates/elab/src/generalize.rs) generalizes later binders only when the scrutinee is a local variable. Extend it to a computed scrutinee: a binder whose type contains the scrutinee term (`==`) is generalized, with its type abstracted to `T[z/e]`, under the same selection rule (an arm names it or the goal mentions it, plus its dependencies).

## Done when
- Probe P1 (`comp_hyp`, design §12.1) checks: in the `False` arm `h` is `False = True`.
- Checked here, and closed if so: [[split-all-revise-hypotheses]], the first half of [[cov-window-in-theorem-arms]], [[nested-match-on-list-tail-motive]].

## Log

- 2026-10-31: Done on PR #318 (design §5.1): refined_by_occurrence generalizes binders whose type contains the computed scrutinee (after every local it mentions), same selection rule; P1 checks (omega_tests.hthr guard_hypothesis_refined; match_refines_hypotheses.rs: open element type, literal, chain, plain fn body by refl, two negative controls). Not closed by it: split-all-revise-hypotheses (Cases builds its own motive in host.rs), nested-match-on-list-tail-motive (the outer Cons arm's goal does not spell the tail as the variable; a field-spelling gap). cov-window-in-theorem-arms is about the wf chain convoy, untouched.

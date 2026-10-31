---
title: Every match arm has the equation scrutinee = pattern, in the term only when read
status: closed
labels: [elaboration,match,proofs]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Slice 1 of [[dependent-match-compiler]] (docs/dependent-match-compiler-design.md §4).

Every arm of every `match`/`split`/`if` has `scrutinee = pattern` in scope: named `h` under `match h:`, otherwise anonymous (a reserved `__` name, unspellable in source, listed by `omega`/`linarith`/`split_all`/`rewrite`/`absurd` and goal display). It starts as a **pending** hypothesis: in the arm's `Cx`, not in Γ. The first resolution unwinds to its match (a `MatchEquationWanted` signal carrying the match's identity), which rolls back and re-elaborates as the convoy (`matching::plan_convoy`). A match nobody reads elaborates to today's term.

## Done when
- Probe P2 (`anon_eq` with `omega` in the `True` arm) and P6 (`half` with no `h:`, design §12.1) check; negative controls stay refused.
- A whole-library `--timings` diff shows identical count columns for every item that reads no equation.
- A function body whose arm listed but did not cite the equation keeps its plain term (§4.3).

## Log

- 2026-10-31: Done on PR #318 (design §4.3.1). Elaborator: pending id in Cx, omega/linarith mark it wanted, a failed arm with a wanted id re-elaborates as the convoy; no unwinding signal, so an arm that listed but did not need the equation keeps its plain term by construction. decreases bodies: AutoEqs binds __dec_meqN only where a lifted obligation quantifies it. P2 and P6 (half, half_unfold) check in omega_tests.hthr with a negative control; decreases_unfolding.rs covers an open element type and an unread candidate. The whole-library --timings count diff was not run: a successful elaboration takes the unchanged path, and a decreases body changes only where its lifted obligation was refused before. split_all/rewrite/absurd do not mark the equation wanted yet.
- 2026-10-31: Amended: the retry is triggered when omega or linarith got stuck with the id in scope, not when they listed it; listing alone cost the creal test a third more time (every refusal in a match arm elaborated twice), stuck-only is master's time.

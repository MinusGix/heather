---
title: Every match arm has the equation scrutinee = pattern, in the term only when read
status: open
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

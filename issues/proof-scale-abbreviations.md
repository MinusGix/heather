---
title: Local abbreviations usable at proof scale
status: open
labels: [frontend,ergonomics,design]
area: language
created: 2026-08-15
updated: 2026-08-15
---



Spun off [[datarepr-surface-ergonomics]] item 6 (2026-08-15). The BinC
hand-runs repeat a five-line recursor spelling a dozen times across one
theorem; the *test file* abbreviates it with a Rust-side helper because
the surface cannot. `let` exists in bodies (bidirectional, good error),
but nothing serves the theorem/file scale: a local abbreviation shared
across a statement and its proof, or across the several theorems of one
certificate. Candidate shapes to weigh: `where`-clauses on declarations,
file-local `def`-abbreviations, or section binders. Interacts with
[[let-inside-quotation]] (what a binding form means inside quoted code)
and whatever [[impl-declaration-surface]] lands (an impl block is a
natural shared-abbreviation scope for its three artifacts).

## Log

- 2026-08-15: PROMOTED to companion piece by the obligation-records round (2026-08-15, round-4 analysis, now docs/language/classes/obligation-records-design.md §1.4 and §9). Inline-first landed: an impl or datarepr clause takes any surface expression, so a proof is written where it is owed and there is no deferral mechanism to park a helper lemma in. That makes this issue the thing that decides whether inline scales — and the round-4 argument is that its answer is BETTER than what deferral would have offered, because a helper inside the proof expression gets exactly the scope it deserves rather than a top-level name sitting between the block and its proof. Concretely for this issue's shapes: the natural first customer is now an inline clause whose proof wants a local abbreviation shared between its own statement and its steps; the impl block as a shared-abbreviation scope for its three artifacts is still open and is the second. If inline proves insufficient at scale anyway, the ledgered fallback is §1.4's adjacent certification region (a 'proof refines { }' block immediately after the declaration, owner implicit), NOT file-wide slots — so a finding here that local abbreviation cannot carry the weight is the trigger to reach for that.

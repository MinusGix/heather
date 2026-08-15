---
title: Local abbreviations usable at proof scale
status: open
labels: [frontend,ergonomics,design]
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

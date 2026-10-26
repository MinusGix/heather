---
title: Give relational rewrites explicit direction and occurrence controls
status: open
labels: [relations,setoids,ergonomics,design]
area: tactics
created: 2026-09-05
updated: 2026-10-26
---

Build on [[proof-position-relational-congruence]]: provide an explicit reverse-step spelling, a way to select or explain changed occurrences, and useful mismatch diagnostics. Keep direction and occurrence choices visible; do not silently guess symmetry, unfold operations, or claim a failed derivation proves a goal false. Validate repeated/partial occurrences, equal witness endpoints, and distinct relations on one carrier. Relational calculation chains remain owned by [[setoid-auto-lifting]]; coordinate their step syntax with this issue.

## Acceptance details

- A reverse step must consume an explicitly reversed proof or suitable symmetry
  evidence for the selected relation. Directional correspondences must not
  acquire symmetry from the spelling of the command.
- Occurrence selection must distinguish repeated and unchanged occurrences and
  report the first unexplained change using the user's expressions.
- Keep unsupported structural derivation separate from a checked refutation;
  counterexample search is optional, never required for ordinary diagnostics.

## Log

- 2026-10-21: the `=` case landed with a spelling this issue should agree
  with or replace (`docs/equation-rewrite-design.md` §1, §3): direction is
  the written proof, reversed only by an explicit `sym(h)`; occurrences are
  `at := k` / `at := [k, …]`, counted from 1 left to right through the goal
  as written, refused past the last with the count, and refused with several
  equations in one call (nest instead).
- 2026-10-26: relation steps landed ([[rewrite-setoid-relations]]). They
  rewrite every occurrence of the left side and refuse `at :=` with a pointer
  here; direction is the written proof, and a symmetric goal side asks for
  `Symmetric` evidence (`?symmetry`) rather than assuming it.

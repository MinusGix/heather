---
title: Say which let multiplies a slow proof, and suggest have
status: open
labels: [elaboration,diagnostics,proofs,performance]
created: 2026-09-25
updated: 2026-09-25
---

When a proof checks slowly because a `let` is copied into its term many
times, nothing says so. The 216 s `read_print_after_read` was found by
bisection ([[proof-let-substitution-cost]]). `have` (docs/have-design.md) is
the fix a person can apply, but only once they know which let to apply it
to.

## Proposal

After an item elaborates, compare its term's tree size with its shared size.
Both are cheap: a pointer set for the shared size, memoized counting for the
tree size. When the ratio is large, report the `let` that contributes the
most paths, and suggest `have` when its value is a neutral application (a
theorem call, or a field of a parameter), since hiding such a value loses
nothing a later conversion could use. In the print proof that is `w`, `st`,
`ln` and `counted` (the anchor issue's 2026-09-25 table).

Open: whether this is a warning on every check or a `check --review` lint
(it adds a walk per item). The rule for lints that re-elaborate does not
apply; this one only walks the finished term.

## Acceptance

- The unsplit print proof, written with `let`s, names at least one of those
  four lets.
- No report on the library as it stands, or each report is a real candidate.

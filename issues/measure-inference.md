---
title: Infer termination measures (size, length, lexicographic) before asking for decreases
status: open
labels: [elaboration,termination,ergonomics]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Item 5, part 1, of the fundamental-improvements memo of 2026-10-31 (Claude Doc, https://claude.ai/artifact/Y2Jo9y9Mgd52QdguvaL43s): a recursive function needs no written `decreases`
when an ordinary measure works.

Try structural recursion first. If that fails, search the obvious measures:
an argument's size or length, then lexicographic combinations, as Lean's
`GuessLex` does. The obligations already default to `omega`
([[termination-measures]]), so the work is the search, plus a refusal that
lists the measures it tried.

## Done when

`gcd`, `merge` and the parser-shaped recursions in the library check with
their `decreases` clauses removed, and a negative control is refused with
the tried measures named.

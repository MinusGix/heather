---
title: Select rewrite occurrences by pattern instead of number
status: open
labels: [frontend,elaboration,proofs,ergonomics,design]
area: tactics
milestone: [tac-general]
created: 2026-10-21
updated: 2026-10-21
---

`rewrite(h, e, at := k)` numbers occurrences left to right through the goal
(`docs/equation-rewrite-design.md` §3). Numbers break silently when the goal
is edited. SSReflect selects by a context pattern —
`rewrite [X in _ <= X]h` — which keeps meaning the same position.

Wanted: a pattern spelling, e.g. `rewrite(h, e, in := λ X => _ <= X)` where
`_` are wildcards and `X` marks the positions to rewrite, refused when the
pattern does not match the goal or marks no occurrence of the left side.
This is the `=` case of [[relational-rewrite-controls]]'s occurrence
selection; design the two together so `=` and relational rewrites share one
spelling.

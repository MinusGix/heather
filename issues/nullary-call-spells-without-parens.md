---
title: A nullary call displays without its parentheses
status: open
labels: [diagnostics,display]
area: language
created: 2026-10-19
updated: 2026-10-19
---

A diagnostic spells the call `ex()` of a parameterless declaration as `ex`,
so a projection out of it reads `(ex).witness`:

```
`refl` needs both sides to be definitionally equal, but `(ex).witness` and `3` are not
```

The display (`crates/elab/src/display.rs`, `Speller::tm`) spells a bare
`GlobalTm` as its name, and a parameterless declaration's call lowers to
exactly that, with no application to show. The same node is also what a
global *referenced as a value* lowers to, so the fix needs the declaration's
arity (`params_at`) rather than a blanket `()`. Found while writing
[[stuck-on-opaque-theorem-diagnostic]]'s tests, which sidestep it with a
one-parameter axiom.

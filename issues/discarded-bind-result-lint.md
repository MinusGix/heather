---
title: Lint a discarded non-True result of an expression statement
status: open
labels: [frontend,lint,ergonomics]
area: language
milestone: [lang-sequencing]
created: 2026-11-01
updated: 2026-11-01
---

docs/language/sequencing-surface-design.md §3.1: `e;` in a block over a carrier whose
result type is not `True` should warn, name the type, and suggest
`let _ <- e;`. Not built with layer 1 (§13 item 7): `e;` lowers in the parser
to `Bind::seq(e, λ #bindN => { let #seqN = #bindN; rest })`, so the warning
needs the solved domain of that generated λ, which the elaborator has when it
checks the λ (`crates/elab/src/binding.rs` recognizes the generated call).
`restore(m);` (a `Tac<True>`) stays silent.

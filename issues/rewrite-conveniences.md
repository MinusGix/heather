---
title: Small conveniences around `rewrite`
status: open
labels: [frontend,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-10-21
updated: 2026-10-21
---

Three small items left from the first `rewrite` round
(`docs/equation-rewrite-design.md`):

1. **Closing by `refl`.** Lean's `rw` tries `rfl` after rewriting. Here the
   body is mandatory (`rewrite(p, refl)`), because with two arguments the last
   could be an equation or the body. A spelling that is not ambiguous —
   e.g. `rewrite(h₁, h₂, ..)` or a named `close :=` — would cover the
   congruence shape.
2. **A block statement.** `rewrite h₁, h₂;` inside a block, rewriting the
   rest of the block's expected type, reads like a tactic script and composes
   with `let`/`on`. New grammar (a contextual statement keyword), so it needs
   the `let-and-blocks` §5.2 rules and the editor inventory.
3. **`calc` steps.** `:= rewrite(h, refl)` in a calc step should already work
   (the step is a checking position); pin it with a test and use it in a
   library chain.

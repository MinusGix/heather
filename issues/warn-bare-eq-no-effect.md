---
title: "Warn on a bare `a = b;` statement with no effect (likely meant `:=`)"
status: open
labels: [frontend,diagnostics]
created: 2026-07-24
updated: 2026-07-24
---

Deferred to when the frontend has a warning mechanism (none yet). Once statement blocks and an effect/assignment form exist ([[goal-holes]] brings block statements; [[effects-direction]] fixes the assignment glyph as `:=`/`<-`), a statement-position `a = b;` is suspicious: `a = b` is a *proposition* (a type), so as a bare statement it computes nothing and discards a value — the author most likely meant the assignment `a := b;`. Emit a warning suggesting `:=`.

Follows the equality-notation decision ([[surface-syntax]], 2026-07-24): merging `=` for binding + equality makes `==` a rejected token, and makes this the one residual foot-gun. Purely a diagnostic — no soundness stake (the kernel gates everything). Blocked in practice on a warnings channel + the statement/effect surface; file now so it is not forgotten.

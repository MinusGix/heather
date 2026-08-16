---
title: "Warn on a bare `a = b;` statement with no effect (likely meant `:=`)"
status: open
labels: [frontend,diagnostics]
created: 2026-07-24
updated: 2026-08-16
---

Deferred to when the frontend has a warning mechanism (none yet). Once statement blocks and an effect/assignment form exist ([[goal-holes]] brings block statements; [[effects-direction]] fixes the assignment glyph as `:=`/`<-`), a statement-position `a = b;` is suspicious: `a = b` is a *proposition* (a type), so as a bare statement it computes nothing and discards a value — the author most likely meant the assignment `a := b;`. Emit a warning suggesting `:=`.

Follows the equality-notation decision ([[surface-syntax]], 2026-07-24): merging `=` for binding + equality makes `==` a rejected token, and makes this the one residual foot-gun. Purely a diagnostic — no soundness stake (the kernel gates everything). Blocked in practice on a warnings channel + the statement/effect surface; file now so it is not forgotten.

## Log

- 2026-08-16: ONE OF THE TWO BLOCKERS IS GONE (2026-08-16): the warning channel exists (docs/diagnostic-warnings-design.md), landed with [[match-arm-redundancy-warning]] as its customer. `Elaborator::warn(msg, span)` raises one, `take_warnings()` drains it, the CLI renders it like an error with the severity word changed, and a warned file still checks and still exits 0 — which is precisely the "purely a diagnostic, no soundness stake" shape this issue asked for. Nothing here was implemented: this issue stays open on its OTHER blocker, which is untouched and is the substantive one — there is no assignment form, so `a := b;` is not a spelling anybody can be advised to write ([[effects-direction]] fixes the glyph). Warning about a bare `a = b;` before the alternative exists would be advice that does not parse, which the diagnostics round just spent a correction learning is worse than saying nothing.

When the assignment form lands, what this issue needs is one `self.warn` at the statement loop's expression-statement case and a test — the channel's §8 records this issue by name as its known next customer.

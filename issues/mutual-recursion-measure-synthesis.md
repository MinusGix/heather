---
title: Structural mutual recursion: synthesize the measure when none is written
status: open
labels: [frontend,elaboration,design]
created: 2026-09-05
updated: 2026-09-05
---



Residue of [[mutual-recursion-declarations]] (docs/mutual-recursion-design.md
§5). `even`/`odd` on `Nat` with no `decreases` does not group: the structural
eliminator hands out no sibling ih, so the measure route is the only one that
generalizes, and today it needs the measure written on every member. Taking
`decreases x` from the descending argument when none is written is a purely
syntactic convenience with real failure modes (which argument, with two; a
declaration silently leaving the structural route it takes today). Decide
whether to do it at all; if so, only for a group whose every member has
exactly one candidate.

## What it assumes from elsewhere
- **[[mutual-recursion-declarations]]** owns the group lowering. Assumed
  here: only that a written measure on every member is what it consumes.

---
title: Auto-refl MVP: an empty proof block discharges by refl
status: open
labels: [frontend,elaboration,syntax]
created: 2026-08-05
updated: 2026-08-05
---

Small round item (2026-08-05 ergonomics round): the one slice of
[[surface-proof-automation]] that issue marks as independent of the
goal-holes engine. `theorem two_two(): 2 + 2 == 4 {}` passes: in checking
position, an empty block gets ONE speculative `refl` attempt, kept iff the
kernel accepts, else the goal stays open. Conservative reading only (the
empty block is the trigger; `refl` never becomes a silent no-op elsewhere).

Scope here: parser accepts `{}` as a proof block; one checking-position
elaborator hook; tests including the negative control (an empty block on a
non-refl goal reports the open goal, not a panic or a silent pass).

## What it assumes from elsewhere
- **[[surface-proof-automation]]** owns the design (conservative-vs-aggressive
  decision, the future solver slot, `apply`). Assumed here: only the MVP
  mechanism as specified there — nothing about `apply` or multi-goal defer.

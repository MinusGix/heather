---
title: Move words between homes, and fix a calling convention for native procedures
status: open
labels: [native,x86]
area: heather-in-heather
created: 2026-10-28
updated: 2026-10-28
milestone: [nh-procedures]
---

A word keeps one home for the whole program
(`docs/native-register-allocation-design.md` §9): no live-range splitting,
no moves at loop edges, and no procedures to call. With procedures (plan
§7, `docs/native-real-programs-plan.md`) the homes need a boundary contract:
which pool registers a callee may write, which it keeps, and where
arguments and results go.

## Scope

- Homes per program point, or per live range, with explicit moves the check
  verifies (a parallel-move resolution proved once).
- The convention: caller- and callee-saved halves of the home pool, argument
  and result registers, and `Held` across a call from it.
- Per-procedure `Homes`, so two procedures may use different allocators
  ([[native-allocator-class]]).

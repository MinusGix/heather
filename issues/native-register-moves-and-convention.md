---
title: Move words between homes, and fix a calling convention for native procedures
status: open
labels: [native,x86]
area: heather-in-heather
created: 2026-10-28
updated: 2026-11-11
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

## Log

- 2026-10-31: docs/native-procedures-design.md §3 fixes the first convention: arguments and results in RDI, RSI, RDX, RCX, R8, R9 (at most six each), homes global, the callee saves its own locals. Every word outside a callee's locals is live across a call to it; per-call-site pass-through sets with per-procedure clobber sets, and moves between homes, stay here.
- 2026-11-01: Revised to caller-saves: a caller pushes every word live after a call but its results and pops them back after; the callee's code may write any home. A per-procedure clobber set, so a caller saves only words whose homes the callee may write, is the refinement that stays here.
- 2026-11-05: gardener: cites a file it shares with [[native-procedure-contracts]] (`docs/native-procedures-design.md`).
- 2026-11-11: docs/native-procedures-are-functions-design.md §2.3 proposes the convention for U5 of [[native-one-compiler]]: the function compiler's (six argument registers, RBX, RBP and R12 to R15 kept, the first result in RAX), the callee saving what it uses, R10 carried in RBX across a call. Per-procedure homes and moves between homes stay here.

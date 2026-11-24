---
title: Proof worlds for native verification: WP/frame, stack-room, and coinductive Bisim
status: open
labels: [native,proofs,itrees,design]
area: heather-in-heather
milestone: [hih-pl-wp]
created: 2026-11-24
updated: 2026-11-24
---

Follow-up to [[proof-worlds]] targeting Heather's native x86-64 / IR / ITree
verification stack:

1. **Weakest-precondition / framing world (`within Wp { … }`):** sequence
   machine or IR instructions with `let r <- step;` while tracking untouched
   register/memory frames automatically (complementing `Kept` record chains and
   eliminating manual frame-threading boilerplate).
2. **Stack-room / resource-budget world (`within Eventually for room`):** use
   `Directed<Nat>(Nat::Le)` for stack-room / memory-budget obligations so
   sub-calls' room requirements combine via `max` automatically.
3. **Coinductive bisimulation world (`within Bisim { … }`):** package guarded
   `CoTree` / ITree bisimulation steps (`Ret`, `Tau`, `Vis`) and up-to laws
   behind a scoped world that lowers to ordinary `M`/coinduction proofs.




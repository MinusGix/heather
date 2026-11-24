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
   register/memory frames automatically — see [[proof-worlds-indexed-wp]] for
   indexed `IxBind` + footprint framing, and `Exec` (`lib/std/relation/exec_world.hthr`)
   for the ordinary-`Bind` forward execution monad over `transition::Star`.
2. **Stack-room & additive resource budgets (`within Eventually for avail`, `within Budget`):**
   use `Directed<Nat>(Nat::Le)` (`Eventually` + `shift`/`split_add`) for max-room
   stack/scratch obligations and additive `Budget`/`Budgeted` for cumulative
   stack-frame / allocation budgets.
3. **Coinductive bisimulation world (`within Bisim` / `within Eutt`):**
   parameterized coinduction (`Paco`) + up-to closures — see [[proof-worlds-paco-bisim]].




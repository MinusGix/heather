---
title: Let words live in registers that the surrounding statements do not use
status: open
labels: [native,x86,perf]
area: heather-in-heather
created: 2026-10-28
updated: 2026-10-28
---

The home pool (`home_pool()`, six registers) excludes every register any
statement may use as scratch (`docs/native-register-allocation-design.md`
§2), so a home changes only when its word is written and `Held` needs no
per-statement clobber facts. RSI, RDI, R8 and R9 sit idle across most
statements.

## Scope

- A clobber set per statement kind (`Stmt::clobbers`), and the check: a
  word whose home a statement clobbers is not live across it.
- `Held` through a statement that keeps every live word's register, which
  `held_kept` already states for leaves.
- A wider pool, and sizes after.

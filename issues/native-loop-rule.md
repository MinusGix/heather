---
title: One loop rule for native code, measured by the history
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-loops]
blocked-by: [native-one-wp]
created: 2026-10-20
updated: 2026-10-20
---

Round P3 of `docs/native-program-logic-design.md` (§6): `loop_at`, one loop
rule for native code.

## Scope

- `loop_at`: an invariant at a label with a ghost variant; the body's `Wp`
  ends either back at the label (with a pass through a syscall, or a lower
  variant) or in `Sim` of the rest. Proved once by induction on the
  remaining history, then the variant.
- Instances: the filter's byte loop (variant: bytes left, no syscall) and
  its read-until-EOF loop (no variant: every pass reads). The write loop's
  short writes are the second I/O instance if the round has room.
- Nested loops are `loop_at` at a leaf of the outer body; no cut-point
  table.

## What it assumes from elsewhere

- **[[native-one-wp]]** owns `Wp`, its `passed` flag and `wp_runs`.

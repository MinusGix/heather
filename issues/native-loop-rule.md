---
title: One loop rule for native code, measured by the history
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-wp]
blocked-by: [native-one-wp]
created: 2026-10-20
updated: 2026-10-20
---

Round S2 of `docs/native-program-logic-design.md` (§6.2): `loop_at`, one loop
rule for native code, which the compiler's `iter` lemma uses.

## Scope

- `loop_at`: an invariant at a label with a ghost variant; the body's `Wp`
  ends either back at the label (with a pass through a syscall, or a lower
  variant) or in `Sim` of the rest. Proved once by induction on the
  remaining history, then the variant.
- Two controls in the round's tests: an I/O loop (read until end of file,
  no variant) and a pure loop (bytes left as variant), each a few items of
  hand-written `Prog`, not a burned process.

## What it assumes from elsewhere

- **[[native-one-wp]]** owns `Wp`, its `passed` flag and `wp_runs`.

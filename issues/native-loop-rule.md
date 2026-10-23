---
title: One loop rule for native code, measured by the history
status: closed
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-wp]
blocked-by: [native-one-wp]
created: 2026-10-20
updated: 2026-10-21
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

## Log

- 2026-10-21: LANDED: `loop_at` in `lib/std/os/linux/linux_x86_64_wp.hthr`, proved by induction on the trace's length (`loop_bound`) then the variant (`loop_variant`), one pass at a time (`loop_pass`). `LoopPost`'s leaving arm is `Holds(v, memory) → Sim(io, t, state)`. Controls in `crates/elab/tests/linux_wp.rs` and `linux_wp_count.rs` (two files, so two test processes under their own rails): `linux_wp_drain` (read stdin to its end, exit 0; no variant, every pass a read) with its exit refused when claimed as exit 1, and `linux_wp_count` (count a frame slot down, exit 0; the slot as variant) with program mutants refused (the wrong slot, the wrong exit status). A wrong-flag mutant of the drain loop is refused too but costs a second drain pass, and counting up runs the kernel out of fuel instead of refusing; neither is in the tests.

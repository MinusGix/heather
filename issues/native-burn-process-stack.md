---
title: Burn the hand-proved native process stack (B1)
status: open
labels: [native,x86,refactor]
area: heather-in-heather
created: 2026-10-21
updated: 2026-10-21
milestone: [hih-program-logic]
---

Burn B1 of `docs/native-program-logic-design.md` (§3.1): delete the
hand-proved process stack (`wc`, `wc -l`, `tr` and the filters, the command),
which the rebuild does not reuse.

## Scope

- Tag the last commit with the stack (`native-v0`) before deleting.
- Delete the `lib/elf64_*` process libraries (keeping `elf64` and
  `elf64_load`), `command_program`, `filter_program`, `filter_step_piece`,
  and the unreferenced older generation (`linux_x86_64_fetch`,
  `x86_64_fetch_block`).
- Delete the read-loop, read-filter and command producers and their
  `build-x86` profiles in `crates/cli/src/native`, their CLI tests
  (`native_wc`, `native_tr`, `native_filter`, `native_read_loop`), the elab
  process tests, and the command warm-up in `scripts/test`.
- Delete `examples/x86-native/{wc,wc_l,tr,tr_s,tr_d}.hthr`.
- Salvage pure specs first: the decimal formatting spec, the filter fold and
  the counts move to `lib/std` with their lemmas.
- Docs of the burned layers get a one-line header pointing here; their open
  issues close as not planned with a link.
- Re-check each deletion by import: a module a kept one imports stays.
- Full `scripts/test` green afterwards; record the suite's new size.

Touches the native support lists (a shared hotspot), so it should not run
beside another native round. Undo is the tag.

## What it assumes from elsewhere

- **[[native-linux-spec]]** owns the Linux model's re-founding; this round
  leaves `linux_x86_64_io` as it is.

---
title: Burn the hand-proved native process stack (B1)
status: closed
labels: [native,x86,refactor]
area: heather-in-heather
created: 2026-10-21
updated: 2026-10-21
milestone: [hih-program-logic]
---

Burn B1 of `docs/native/native-program-logic-design.md` (§3.1): delete the
hand-proved process stack (`wc`, `wc -l`, `tr` and the filters, the command),
which the rebuild does not reuse.

## Scope

- Tag the last commit with the stack (`native-v0`) before deleting.
- Delete the `lib/elf64_*` process libraries (keeping `elf64`, `elf64_load`,
  `elf64_io`, which `x86_64_fetched_code` imports, and `elf64_calls`, the call
  examples' library), `command_program`, `filter_program`, `decimal_line`,
  `field_line`. `filter_step_piece`, `linux_x86_64_fetch` and
  `x86_64_fetch_block` stay for B2: the call path and the structured
  generator import them (design §3.1, as corrected).
- Delete the read-loop, read-filter and command producers and their
  `build-x86` profiles in `crates/cli/src/native`, their CLI tests
  (`native_wc`, `native_tr`, `native_filter`, `native_read_loop`), the elab
  process tests, and the command warm-up in `scripts/test`.
- Delete `examples/x86-native/{wc,wc_l,tr,tr_s,tr_d}.hthr`.
- Salvage pure specs first: the decimal formatting spec moves to
  `lib/std/text/decimal.hthr`; the counting lemmas join the filter fold in
  `stream_filter`.
- Docs of the burned layers get a one-line header pointing here; their open
  issues close as not planned with a link.
- Re-check each deletion by import: a module a kept one imports stays.
- Full `scripts/test` green afterwards; record the suite's new size.

Touches the native support lists (a shared hotspot), so it should not run
beside another native round. Undo is the tag.

## What it assumes from elsewhere

- **[[native-linux-spec]]** owns the Linux model's re-founding; this round
  leaves `linux_x86_64_io` as it is.

## Log

- 2026-10-21: Done in this round's PR. Deleted: 18 elf64_* modules, command_program, filter_program, decimal_line, field_line; the read-loop/read-filter/command producers and evaluate.rs; filter_step.rs; 17 elab process tests and their warm-ups; native_wc/native_tr/native_filter/native_read_loop; the five stdin examples. Kept (corrected in design §3.1): elf64_io (x86_64_fetched_code imports it), elf64_calls, linux_x86_64_fetch, x86_64_fetch_block, filter_step_piece, order.rs, support.rs: all on the call path or the structured generator, so B2's. Salvaged: lib/std/text/decimal.hthr; the counting fold lemmas joined stream_filter. crates/elab/tests/native_foundation.rs checks x86_64_asm, stream_filter, filter_step_piece and decimal, which nothing else imports now. Full scripts/test on the cloud box, warm stores: 3433 passed, 0 failed, 5 ignored, ~5 min wall (it was ~13.5 min, 3229 passed before the command rounds' tests were added to it and these removed). The native-v0 tag (189659d) could not be pushed from the cloud box; Minus pushes it.

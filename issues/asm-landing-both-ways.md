---
title: One landing check for label jumps, forward and back
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-wp]
created: 2026-10-21
updated: 2026-11-26
---

`Prog::laid_out` (`lib/std/arch/x86_64/x86_64_asm_runs.hthr`) asks every
JCC/JMP to land forward on its label (`jumps_land`), which is what the
structured lowering needs. A loop jumps back, so `Wp`
(`lib/std/os/linux/linux_x86_64_wp.hthr`) checks landings with its own Bool, `wp_reach`,
which accepts either direction (`asm_item_lands || asm_item_lands_back`) and
proves the landing (`wp_lands`) from it.

Two checks over the same items is cruft: make `jumps_land` accept both
directions (it is a Bool checked by evaluation either way), prove
`wp_lands` from it, and drop `wp_reach`. The function-IR round adding calls
(PR #106) also changes what lands where (a call's target, both ways); fold
this in after it merges, so there is one landing notion for jumps and calls.

## What it assumes from elsewhere

- **[[native-one-wp]]** owns `wp_reach` and `wp_lands`.
- **[[function-ir-verified-lowering]]** owns `laid_out` and the structured
  lowering's use of it.

## Log

- 2026-10-24: 2026-10-24: `wp_reaches` now also lands `CallTo` on its label, both ways ([[wp-stack-items]]); the one landing check this issue makes covers calls too.
- 2026-11-26: From [[bytes-level-access-view]]: a JCC still lands only forward.
  - JMP and CALL land both ways: `item_lands` takes `asm_item_lands || asm_item_lands_back`.
  - JCC and JCC-short take `asm_item_lands`/`asm_short_lands` alone, and `JccLands` is `JumpsForward`/`ShortForward` only.
  - So `Prog::laid_out` refuses a loop whose back edge is a conditional jump (one jump per continuing pass, no second instruction). The bytes level's loop tail therefore jumps forward out and takes one JMP back.

  To allow it:
  - Add the back alternatives for `Jcc`/`JccShort` to `item_lands`, a backward `JccLands`, and its step lemma.
  - Every consumer that derives `JumpsForward` from `laid_out` then needs either direction:
    - `jcc_lands`, `jcc_item_lands` and `Site::jcc_item_steps`;
    - `test_by_steps`, `moves_test_by`, `claims_test_by` and `runs_branch_on` (std);
    - the structured lowering's branch and loop proofs (`function_ir_lower_structured`, `function_ir_lower_calls`), `native_compile_steps`, and bytes_level_lower.
  - An improvement for after the switch to the bytes level: it changes a model the old pipeline's proofs lean on.

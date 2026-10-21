---
title: One landing check for label jumps, forward and back
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-wp]
created: 2026-10-21
updated: 2026-10-21
---

`Prog::laid_out` (`lib/std/arch/x86_64/x86_64_asm_runs.hthr`) asks every
JCC/JMP to land forward on its label (`jumps_land`), which is what the
structured lowering needs. A loop jumps back, so `Wp`
(`lib/linux_x86_64_wp.hthr`) checks landings with its own Bool, `wp_reach`,
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

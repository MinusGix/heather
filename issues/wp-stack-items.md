---
title: Wp arms for calls, returns and stack slots
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-wp]
created: 2026-10-21
updated: 2026-10-22
---

S4 round 3 (PR #106) added `CallTo`, `Ret`, `Spill` and `Reload` to `Asm`.
`Wp` (`lib/linux_x86_64_wp.hthr`) was written alongside it, and leaves all
four `False` (its catch-all, and `false_elim` arms in `wp_item_goes`), so a
program with them can be checked by `Wp` only if they are never reached.

## Scope

- `Spill`/`Reload`: a stack view (or the frame view grown with stack slots),
  its `Stores`/`Word` arms stated for RSP-relative slots, sound against
  `x86_64_stack`'s step lemmas.
- `CallTo`/`Ret`: a call enters a callee by a contract, as `Proved` does,
  which `x86_64_stack`'s callee contract may be; a return is a leaf.
- Landing: see [[asm-landing-both-ways]], which folds a call's target into
  the one landing check.

## What it assumes from elsewhere

- **[[native-one-wp]]** owns `Wp` and the view interface.
- **[[function-ir-verified-lowering]]** owns the stack items and their
  run lemmas.

## Log

- 2026-10-22: A `Stack` over the byte model exists with its laws proved: `DataRegion::stack` (`lib/std/arch/x86_64/x86_64_byte_memory.hthr`, [[memory-model-machine-instances]]). A stack view for `Spill`/`Reload` can be stated over it.

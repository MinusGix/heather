---
title: Wp arms for calls, returns and stack slots
status: closed
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-wp]
created: 2026-10-21
updated: 2026-10-24
---

S4 round 3 (PR #106) added `CallTo`, `Ret`, `Spill` and `Reload` to `Asm`.
`Wp` (`lib/std/os/linux/linux_x86_64_wp.hthr`) was written alongside it, and leaves all
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
- 2026-10-24: 2026-10-24: LANDED. Linux's step had no stack forms (`LinuxStep` was fetched ∨ store), so first it became x86_64_stack's `MachineStep` at the profile's accesses: the step-form decoder reads a frame slot (mod 01, r/m 100), RET (`c3`, one byte) and CALL (`e8`), and `StackForm::executes_respects_defined` keeps determinism. In `Wp` (`lib/std/os/linux/linux_x86_64_wp.hthr`): `Spill`/`Reload` are the view's `Stores`/`Word` at `stack_address` (no stack arm: a stack view is any view that knows those addresses; `ViewSound.stores` now also gives the canonical bound the stack forms ask); `CallTo` stores its return address through `Stores` and enters the function at its label by a `Callee` contract from a second table (`callees: Nat → Callee<M, V>`, keyed by label), over the view since a call changes memory; `Ret` is a leaf at the popped word. `Callee::Returns` is in continuation form, so a function's body is proved by `Wp` itself (`Callee::returns_by`); `Callee::returns_of_steps` takes steps to a return (what `Site::Returns` gives, with `linux_steps_of_machine`). `wp_reaches` lands calls both ways. Control: `crates/elab/tests/linux_wp_call.rs` (the frame as the stack; a function that spills, reloads and returns), with two refused mutants; determinism gets three decoder mutants. Design §6.5. Follow-up: [[wp-callee-from-lowered-function]] (S4's `Site::Returns` as a `Callee`).

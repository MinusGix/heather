---
title: Size a compiled function's frame by what it uses
status: closed
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes,nh-library]
created: 2026-11-12
updated: 2026-11-16
---

Every function the verified lowering emits opens a frame of 112 bytes: eight slots for the caller-saved registers a call stores round itself and six for the callee-saved registers a function may save (`frame_allocate`, `function_opened`, `lib/native/function_ir/function_ir_lower_calls.hthr`). The size is one constant so that the body's theorems speak of one depth. A leaf that saves nothing uses none of it ([[function-ir-verified-leaf-frame]] is that case), a caller that saves nothing uses 64 bytes, and only a function that saves all six uses the whole.

The cost is in the contract and not in the instructions: the stack an export states is 120 bytes for every function before it in its program (`120 * Succ(f) <= i` in `compiled_returns`). It was 72 before a function could save ([[function-ir-values-in-kept-registers]]). [[linked-program-entries-limits]] has the other half of the same figure: the bound counts a function's index, not what it calls.

## What it takes

- The frame as a function of the function: no slot for a leaf's calls, `8 * saves` for its saves, the saves directly above RSP in a leaf. The count is already threaded through the body's theorems (`saves`); whether a body calls is `StructuredRegion::calls`. `function_runs` takes the frame's size as it takes the count today, and the save slots' place (`Stack::saved_above`, slot 8 on) becomes the size of the spill area.
- The contract's room by function: a table of depths, a function's own frame and return address plus the deepest of the functions it calls, in place of `120 * Succ(f)`. (Half built 2026-11-16, [[stack-room-by-call-depth]]: the room is `136 * Succ(depth(f))` by a table of call depths the lowering computes and checks, `program_depths` and `program_shallow`; what is left here is a level's size by the frame each function actually uses, in place of the one 136.) `lower_program_correct` is already an induction over the program in that order, and `compile-x86` already writes a figure per export into the file's stack line (`Signature::stack`, `crates/cli/src/native.rs`).
- The statement compiler's bound (`128 * functions`, `native_compile_function.hthr`) follows the table.

## Done when

A leaf export that saves nothing states the eight bytes of its return address, and `scan_token`'s line is the sum of the frames on its deepest path.

## Built (2026-11-16)

A function's frame is `8 * (slots + saves)`: eight call slots where its body calls and none in a leaf, the saves directly above them (`Function::frame`, `call_slots`, `frame_size`, `function_ir_lower_calls.hthr`). The body's theorems are bound by the frame's top (`w`) in place of the one depth, and a call's guard is `Stack::CallFrame`.

The contract's room is a table `rooms: Nat → Nat`, a parameter of every program theorem (`lower_program_roomed`, `lower_program_roomed_correct`, `_needs`, `_quiet_correct`; `compiled_returns*`, `compiler_correct*`, `Ending::returns_*` take it after the placement). The lowering checks each function against its row (`Function::roomy`: the frame fits, a call's 24 bytes below it, each callee's row below that, `StructuredRegion::Fits`), so any table it accepts is sound and the table is a choice, not a premise to trust. `program_rooms_by(functions, saves)` is the least table for a count of saves per function: its frame and the deepest callee's room with the call's 24 bytes. `program_room` (every function saving six) is the table `lower_program` and `lower_program_lent` keep, `program_room_planned` the planner's; `compile-x86` reads each function's saves off its placement, states the table as a literal (`{prefix}_rooms()`) and lowers under it.

Figures (`STACK:` in `crates/linked/generated/exports.rs`): every leaf that saves nothing, `sha256_t2` among them, 136 → 0; `scan_accept` 0; `scan_token` 680 → 400; `List::scan_tokens` 816 → 520; `Sha256::compress` 1,088 → 656; `Sha256::update` 1,496 → 936; `copy_window` 272 → 88.

Left, not this issue's:
- An empty frame still opened and closed with `ADD RSP, 0`; closed by [[function-ir-verified-leaf-frame]].
- The statement compiler's functions (`Prog::links`) were emitted under `index_rooms()` (`136 * Succ(g)`). 2026-11-16: they are emitted under `program_room` (every function saving the six registers it may, so no placement exceeds it and the bound needs nothing of `homes.places`), and a statement activation keeps `program_calls_room` below its frame (the table's largest room and the CALL's word) in place of `144 * functions.len()` (`Target::roomy`, the `deep` premise of `Source::elf_file_simulates` and the write-elf certificates).


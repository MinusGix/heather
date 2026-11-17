---
title: Size a calling function's call slots by the words its calls spill
status: closed
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-16
updated: 2026-11-16
---

A function that calls reserves eight call slots (`call_slots(calls)`, 64 bytes, `function_ir_lower_calls.hthr`): room for every caller-saved register a call may have to store round itself. A call stores only the values live across it, so most callers use one or two slots. Since [[function-frame-sized-by-use]] the frame is `8*(call_slots + saves)` and each function is checked against its room (`Function::roomy`), so the slot count is the remaining fixed cost in a caller's frame (`scan_token` 400, `Sha256::update` 936 in `crates/linked/generated/exports.rs`).

What it needs: the slot count read off the body (the largest number of words any call in it spills, `StructuredRegion` walked as `callee_room` is), `Function::slots` returning it, and the call step's premise `slots = 8` (`called` in `function_runs_saved`) becoming "the call spills at most `slots` words". `Loan::stable_saved` places the saves above the slots, so the saves' offsets follow the count as they already follow `slots`.

## Resolution

Built as a placement head the lowering checks, not a count it trusts. A calling function's placement may carry `CallSlots(n)` after its `Saving(s)` (`placement_slots`, eight with no head); `Function::slots(asked)` is `asked.min(8)` where the body calls and 0 in a leaf, and the frame is `8*(slots + saves)`. Each call is checked against it at emission (`saves_ok(slots, saved)`: what the call saves fits the slots, at most eight, every one caller-saved; `call_refusal` names it), and the call proofs run over any `slots` (`Stack::CallFrame(top, avail, d, slots, …)`, offsets `d + 8 * slots`), so the `slots = 8` premise is gone from `function_runs_saved`. The planner asks for the most any one call saves (`places_slots`); `program_rooms_by` takes each function's asked slots beside its saves, and `compile-x86` reads both off the head (`Place::number`: `CallSlots` is 24 and the count, `Spilling` moved to 33 and the mask so a count of eight stays apart from mask 0).

Stack figures (`exports.rs`): `scan_token` 400 → 184, `Sha256::update` 936 → 552, `Sha256::finish` 920 → 488, `Sha256::compress` 656 → 352, `List::scan_tokens` 520 → 384, `scan_step` 176 → 64, `count_newlines`/`copy_window` 88 → 24. Tests: `function_ir_spills_tests` (head reading, planned slots, a too-small head refused), `function_ir_saves_tests` (frame by asked slots).

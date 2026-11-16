---
title: Size a calling function's call slots by the words its calls spill
status: open
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-16
updated: 2026-11-16
---

A function that calls reserves eight call slots (`call_slots(calls)`, 64 bytes, `function_ir_lower_calls.hthr`): room for every caller-saved register a call may have to store round itself. A call stores only the values live across it, so most callers use one or two slots. Since [[function-frame-sized-by-use]] the frame is `8*(call_slots + saves)` and each function is checked against its room (`Function::roomy`), so the slot count is the remaining fixed cost in a caller's frame (`scan_token` 400, `Sha256::update` 936 in `crates/linked/generated/exports.rs`).

What it needs: the slot count read off the body (the largest number of words any call in it spills, `StructuredRegion` walked as `callee_room` is), `Function::slots` returning it, and the call step's premise `slots = 8` (`called` in `function_runs_saved`) becoming "the call spills at most `slots` words". `Loan::stable_saved` places the saves above the slots, so the saves' offsets follow the count as they already follow `slots`.

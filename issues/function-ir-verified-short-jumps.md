---
title: Assemble the verified lowering's jumps in their short forms
status: closed
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-24
updated: 2026-11-16
---

The verified lowering's `Prog` assembles every `Jcc` as `0F 8x rel32` and
every `Jmp` as `E9 rel32` (`x86_64_asm`: an item's length is fixed, 6 and
5 bytes, so offsets are computed in one pass). The branches in
`examples/x86-native/branches.hthr` all jump a few bytes, where the
rel8 forms (`7x rel8`, `EB rel8`) are 2 bytes each: a one-armed
conditional pays 7 bytes over the old per-function path, which emitted
the short forms. After [[function-ir-verified-selection-rules]] this and
[[function-ir-verified-leaf-frame]] are the whole gap on the
branch examples.

What it needs: an item length that depends on the displacement, so
layout becomes a fixed point (relaxation). The usual safe shape is to
start every jump short and lengthen any whose displacement does not fit
until nothing changes; lengths only grow, so it terminates. The step
semantics already decode both forms (`x86_64_step_forms`: `EB rel8` and
`70–7F rel8`), and `x86_64_block` spells both opcodes. The proof side is
`Site::Runs` over the assembled bytes, which reads each item's length
from the layout: the lemmas that read a `Jcc`/`Jmp` need a case per
form, and the layout's offsets come from the relaxed lengths instead of
`asm_length`.

Cost to watch: the certificate states the layout as a literal and checks
it by `refl` ([[function-ir-verified-compile-cost]]); relaxation adds
passes to that evaluation, bounded by the number of jumps.

## Resolution (2026-11-16)

Built without making an item's length depend on the layout inside the
proof. `Asm` gains `JccShort` and `JmpShort` (two bytes, `short_rel`), and
`Prog::jumps_land` checks them as it checks the near forms: a short JCC
lands ahead within a signed byte (`ShortForward`), a short JMP either way
(`ShortBack` too). The lowering picks a form per label from a hint, the
placement's `Short(name)` places after its `[Saving]? [CallSlots]?` head
(`placement_short`, `shorts`), threaded through `emit_calls` and every
branch and loop lemma (`jcc_item`, `jmp_item`, `Site::moves_branch_by`,
`Site::moves_test_by`, `Site::runs_jump_item`). The hint is untrusted like
any place: a label hinted short whose jump does not reach is refused by
`laid_out`, and `lower_program_correct` holds for whatever the hint says.

Relaxation is compile-x86's, in Rust (`labels::relax`): every jump to a
label of the function starts short, a label any of whose jumps does not
fit goes back to near, until nothing changes. The function's items are
then stated with the short forms and its placement with the `Short`
places, and the certificate's emission of that placement checks the
prediction by `refl`; no second read.

Probes and controls: `lib/_tests/native/function_ir/function_ir_short_jumps_tests.hthr`
(a branch both ways short, seven bytes off; a loop whose jump back is a
short JMP behind; a JCC hinted short over an arm past a signed byte is
refused; a short JCC behind does not land).

Linked code, certified bytes before and after: scan_token 12478 → 10250,
scan_tokens 15590 → 13257, Sha256::compress 9035 → 8226, Sha256::update
9844 → 9003, Sha256::finish 10471 → 9629, count_newlines 347 → 291,
copy_window 397 → 313.

Not covered: the statement compiler's own jumps (`native_compile.hthr`)
are still near; it would take the same hint in its procedures.

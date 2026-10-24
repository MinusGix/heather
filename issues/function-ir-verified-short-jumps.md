---
title: Assemble the verified lowering's jumps in their short forms
status: open
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-24
updated: 2026-10-24
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

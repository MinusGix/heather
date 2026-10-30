---
title: After ofNat is one word, attribute what native certificate pieces still spend
status: open
labels: [kernel,native,performance]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-30
updated: 2026-10-30
---

Follow-up to [[native-encoder-ofnat-cost]], closed when `ofNat` at closed
arguments became one word in the kernel (`cert/yes-pieces` 488,749 →
327,015 steps, kernel 0.97 → 0.57 s on cloud). The remaining two thirds of
the steps are not `ofNat`; the earlier profile named `Nat::add` (the
`add_nat` address arithmetic) next. Re-run the per-definition δ-unfold
profile on `yes_tool_elf_piece_1_is` and decide the next lever from it.

Also worth re-measuring now: packing write-elf's immediates as literals
(refused in #269 because the lowering's `ofNat` met them at the spine for
free; both sides are now words).

## Done when

`cert/yes-pieces`'s remaining cost is attributed and either cut or its
reason written down.

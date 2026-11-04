---
title: After ofNat is one word, attribute what native certificate pieces still spend
status: closed
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

## Resolution (2026-10-30)

Attributed with a throwaway per-site step tally (`#[track_caller]` on
`Eval::spend`, a global counter per caller line, a separate image store for
the instrumented binary since a kernel edit discards the verdict store) and
`--only` probes per instruction kind. `Nat::add` was not it: on
`yes_tool_elf_piece_1_is` (40,875 steps) about 44 % of the steps were
**fold-class probes**, and the 46 `MovRI`s (≈5.1 K steps each, their eight
immediate bytes) were ≈72 % of the pieces; a `MovRR` was ≈1.3 K.

The probes repeated because the fold-class memo was keyed by the step
closure's address, and every δ-unfold of `take_low`, `drop_low`, `mul` …
allocates a fresh step closure over that call's arguments — even when the
step reads none of them. The kernel now keys a closure by what its body
reads (`TmClo::closed_ident` / `ident_under`, the bounds memo's footprint,
the same reading conversion's closure identity makes): the fold-class and
transducer memos past the step's (motive's) own binders, and a new
closed-value memo, so a constant inside a definition (`Nat::pow(2, 32)` in
`near_rel`) is evaluated once per query. No definition is named.
`crates/kernel/DESIGN.md` has the paragraph; two kernel unit tests pin both
memos and the negative (a step reading a capture stays per closure).

`scripts/bench-probes --filter cert/ --samples 5` on cloud, master 1ad40d5
against this branch, each over its own warmed store:

| case | steps | kernel s |
| --- | --- | --- |
| `cert/yes-pieces` | 327,015 → 198,619 (−39 %) | 0.30 → 0.15 |
| `cert/yes-labels` | 29,897 → 29,897 | 0.17 → 0.17 |

A cold check of `lib/std/arch/x86_64`'s closure (`--world lib`, width
one): 29.79 M → 29.18 M steps, no item's count up, the x86 decode and
step-form lemmas 20–30 % down; gate seconds 224.9 / 237.1 (master, two
samples) against 225.4 (branch).

What a piece still spends is spread over the inductive representation —
β, `Fst`/`Snd` of constructor records, `case` on tag sums, `El` decodes —
with no single site; the transducer's one-unit-per-bit charge is a share of
the steps but not of the seconds. Two smaller levers seen and left:
`near_rel`'s `Nat::pow(2, 32)` still probes `mul`'s step once per
multiplication, once per piece (its captured multiplicand differs each
time); and `imm_byte_k`'s chain of drops (`imm_rest_k` re-dropped per byte)
is ≈10 % of a `MovRI` over one drop per byte. A closed-value memo for type
closures was tried and bought nothing. Packing write-elf's immediates was
not re-measured this round.

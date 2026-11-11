---
title: A leaf's emission is mostly membership scans over lists of word ids
status: open
labels: [performance,native,compiler]
area: heather-in-heather
created: 2026-11-11
updated: 2026-11-11
---

Found by [[native-tool-compile-attribution]], after its reads stopped repeating one another.

What is left of a native tool's `write-elf` is the compiler's own evaluation: each leaf is emitted once by the fork's read (`{p}_read_#_part`) and once by the kernel (`{p}_e_#`), and both run the library's `Stmt::emits` in the evaluator. A profile of the reads by the definition being unfolded says where that goes.

## Measured

2026-11-11, four-core cloud box, `sort_tool` cold, dev-profile binary at width one. The reads of the parts are 18.0 M evaluator steps (17.5 M of them the 127 whole parts' emissions, about 60 thousand a leaf). Charging each step to the definition most recently unfolded (a flat attribution: a caller's work after a call returns is charged to the callee):

| definition | steps | unfoldings |
|---|---|---|
| the global at position 75, by its place and count `Bool`'s generated eliminator (every `match` on a verdict) | 4.48 M | 633 k |
| `Nat::same` | 3.13 M | 260 k |
| the global at position 33, by its place and count `Or`'s generated eliminator (the `match` on `eq_dec`'s answer) | 1.22 M | 244 k |
| `function_ir_eval::absent` | 1.21 M | 158 k |
| `List::nth` | 0.82 M | 16 k |
| `Bool::and` | 0.77 M | 257 k |
| `Nat::eq_dec` | 0.72 M | 240 k |
| `Nat::differs` | 0.70 M | 234 k |
| everything else (1,255 definitions) | 4.95 M | |

So about two thirds of the compile's evaluation is one chain: `absent(id, ids)` scanning a list of word ids, each element through `Nat::differs`, which asks `Nat::eq_dec` for a proof-carrying answer (`Inl`/`Inr`), which asks `Nat::same`, and the verdict is matched three times on the way back (in `eq_dec`, in `differs` and in `&&`). That is about fifty evaluator steps for each element scanned, and a leaf scans about a thousand elements (liveness, apartness and the pass's `needs` are all list sets of ids).

The kernel's side has the same shape: its 127 whole-part statements are 14.8 M steps.

## Directions

- The constant: `Nat::differs` and `Nat::matches` as `Nat::same` and its negation, with `differs_ne` and its siblings proved from `same_sound`/`ne_of_same`, so a comparison builds no `Or`. `absent` could match on `same` directly. This is a change at the root of `lib/native/function_ir`, so every native module re-elaborates, and proofs that unfold `differs` through `eq_dec` need their step restated.
- The exponent: the sets as something a membership test does not scan. Word ids are small and dense, so a set as a `BitVec` (the kernel has native bitvector values) makes `absent` one `testBit` and union, difference and `within` one word operation each. That is a representation change across `native_alloc` and `native_compile` and their proofs, worth a design note first.
- Either way the measure is `scripts/bench-probes --heavy --filter native/elf-cold` (`eval_steps` on `sort_tool` and `tac_tool`), and the reads' and the `e_#` rows' steps per leaf.

## Done when

A leaf's emission costs visibly fewer steps on `sort_tool` and `tac_tool` cold, in the read and in the kernel's statement both, with the ELF bytes unchanged.

## Log

- 2026-11-11: measured the constant on a scan by itself, and tried the first direction. A probe file with three spellings of `absent` over a 400-id list (one `refl` each, kernel steps from `--timings`): today's (`differs` through `eq_dec`) is 37 steps an element, `differs` as a match on `Nat::same` 28, and `absent` matching on `same` itself with no `&&` 19. So the first direction is a quarter of a scan, and the second spelling a half, and what is left is the evaluator's own price for a `match` on a list and a call.
    - Rewriting `Nat::differs` and `Nat::matches` over `same` keeps `function_ir_eval` whole with six proofs restated (`differs_ne`, `matches_eq`, `differs_of_ne`, the two `reflects`, `absent_false_mem`), but proofs elsewhere reach the old spelling by matching on `eq_dec`: four that write the motive out (`List::known_holds` in `function_ir_pass`, `Env::knows_known` in `native_compile_segments`, `Tm::differs_of_ne` in `rt_loop`, `Loc::clear_join` in `rt_io_lower`), the copies of `differs_true`, `matches_false` and `differs_eq_of_ne`, and at least four more in `function_ir_pass` that match on `eq_dec` and let the goal follow (`forget_holds`, `needs_unwritten`, `pruned_last`, `fold_runs`'s callee). I stopped there: `rt_loop`, `rt_io_lower` and `native_structured_meaning` are files #551 rewrites, and a quarter of a scan is not worth a conflict with it. The patch as far as it went is kept outside the repository (the project files, `native-perf/differs-same.diff`); redo it after #551 lands, or go to the bit sets directly.
    - The exponent, measured across the tools (cold `write-elf`, the certificate's `e_#` rows): `head_n_tool` 119 statements and 6.5 M steps, `tac_tool` 213 and 15.1 M, `sort_tool` 260 and 23.5 M. The median statement is 38, 58 and 70 thousand steps, so a statement costs more the larger its program is, and the whole grows about as the statements to the power 1.65. A leaf's own work does not grow; the sets it scans do (ids live across it, ids to stay apart from). That is the case for the second direction over the first: a program ten times `sort_tool` would be about forty-five times its steps as the lists stand.
- 2026-11-11: what the second direction can count on, measured (kernel steps and gate time of `refl` probes, dev-profile binary). The kernel's native bit runs stop at 64 bits (`BIT_RUN_WIDTH_CAP`), so a set as one `BitVec` of the program's id count is not one operation: `bor` of two 512-bit vectors checked against a literal is 22 thousand steps and 0.6 s, structural all the way. At 64 bits an operation is native: 200 rounds of `bor`, `band` with a `complement`, `bor` cost 5.5 ms, about 7 µs an operation, which is what scanning one list element costs today. So the representation is a list (or a `nat_map`) of 64-bit words: a union or difference of two sets over 500 ids is 8 word operations where the lists do tens of thousands of element steps, and membership is a walk to the word and one mask. `Nat` as the bit set is out: dividing by `2^300` to read a bit ran out of fuel.
    - The shape that does not rewrite the proofs is the one `Homes::nodes_checked` already has beside `Stmt::checks` ("the same checks with each set computed once", proved equal by `Stmt::checked_sound`): a twin of the evaluated functions over word sets, proved to agree with the list ones once, which the certificate's statements evaluate. The list definitions and everything proved about them stay, so it is additive to what #551 changes.
- 2026-11-11: what a design note has to decide, from reading where the sets go. The live-out list `out` is not only the checks' (`Stmt::checked`, `Homes::apart`, `misses`): it is an argument of the emission itself (`Prog::word_from`, `ports_from`, `leaf_into`, `reads`, `writes`, every `Prog::…(layout, out, …)` in native_compile), which asks it membership questions to drop dead stores. So there are three shapes, in rising cost: (a) a twin of the checks alone over word sets, proved equal as `Stmt::checked_sound` is, which leaves emission's scans; (b) the twin carried through emission, which duplicates `Prog`'s functions; (c) the set's type made abstract (`has`, `union`, `minus`, `within` and their laws against `Mem`), with lists and word sets as two instances, which touches about five hundred uses across twenty-five files once and then lets the representation change freely. A fourth direction is orthogonal: find why a statement's sets grow with the program (which ids stay live across unrelated parts) and scope them. The first step of the note is a count of scans by caller on `sort_tool` (the per-definition profile, by the caller of `absent` and `misses`), so the choice between (a) and (c) is made on which callers pay.
- 2026-11-11: Correction to the scaling entry above. The claim that emission grows as the statement count to the 1.65 because the id sets grow with the program is wrong, and so is the case it made for bit sets. The live-out sets are small: `sort_tool`'s 260 have a median of 14 ids and a largest of 23, `tac_tool`'s a median of 13, `head_n_tool`'s a median of 5, and every id of these tools is under 64. Two other things grew with the program. Each statement worked the program's layout out again, a walk of the whole program ([[native-certificate-layout-per-item]], fixed). And each join of a sequence has the kernel work out the liveness of everything after it, which is quadratic in the length of a straight run ([[native-emission-join-liveness]], the common case fixed, the rest and the design that retires it filed there). What this issue describes, the scans inside one leaf's emission, is the 7.7 M steps of `sort_tool`'s parts that are left: a constant a leaf, not a growth.

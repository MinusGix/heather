---
title: The ELF header mutation test paid 1.9 s per module to check a 176-byte list literal, not to refuse a conversion; vector literals were quadratic in the kernel
status: closed
labels: [testing,x86,performance,kernel,elaboration]
created: 2026-09-11
updated: 2026-09-11
---

`crates/cli/src/native/elf.rs::elf_header_mutations_are_rejected_by_heather` builds 28 one-theorem modules — the static header against `static_elf64_header` by `refl`, once accepted and 27 times with one bit flipped and refused as NotConvertible — at 88 s serial on furnace (2026-09-11), the single largest unit test in the suite.

**The premise this was filed under was wrong.** Measured per module (release `heather check`, furnace, one probe per module, 3.4 s load baseline): the `header_agrees` theorem costs 16 ms accepted and 27 ms refused (11 ms of that the diagnostic note), at any offset of the flipped byte. The 1.93 s is the kernel gate on the *definition* `actual_header`, identical in all 28 modules: 6.2 M eval steps to check a 176-element `[…]` literal against `List<BitVec(8)>`. The failed-conversion path ([[kernel-failed-conversion-cost]]) has no customer here, and neither the mutation count nor the parallel gate ([[parallel-kernel-gate]]) is the lever.

## The defect

Two spellings, one shape. The conversion-miss trace on `actual_header` is one family: 177 `Vec/Σ` misses whose cost grows linearly with depth (3 µs at the innermost pair, 39 ms at the outermost; 3.0 s traced), because

- a collection literal lowers (`Elaborator::check_collection_literal`, `ExprElab::check_vec_lit`) to an n-deep nested `pair` whose every level is annotated with its tail type `Vec(T; k)`;
- the kernel's evaluator reduces a `Vec` at a canonical length eagerly into its `Σ` encoding, and its `Vec`/`Vec` congruence was reached only at a *neutral* length — so the tail annotation at depth k was compared with the expected `Vec(T; k)` by unfolding both into a k-deep `Σ` chain, comparing the element type (the 606-node decoded `BitVec(8)` code) once per level: `n²/2` element comparisons;
- `inductive::nat_lit` spelled those lengths as unary `Succ` chains although the kernel has `NatLit`, making the annotated term itself quadratic in the literal.

The generators knew: `native.rs::byte_chain` ("a file-sized `[…]` literal … costs seconds on its own") and the offset-wise byte theorems route around it.

## The fix (2026-09-11)

- **Kernel**: `Conv::vec_ty` — two sides both *spelled* `Vec` (`Dom::vec_former`: `Type::Vec` syntax, or the unforced `TyClo::Vec` tail the evaluator leaves) are decided before either reduces: lengths as `Nat` terms, then the elements once unless the length is zero. The verdict is the encoding's in every case (equal canonical lengths: elements decide, or `Unit` at zero; different canonical lengths, or canonical against neutral: never; two neutral: the structural rule as before), so nothing falls through and nothing is retried. `docs/kernel/wf-former-design.md` §5.
- **Elaborator**: `nat_lit` emits `NatLit`.
- **Pins**: `crates/kernel/tests/vec_fin.rs` (verdicts at zero / equal / different / neutral lengths, against the encoding, and the literal at the elaborator's shape at 256 elements); `crates/elab/tests/surface_fin.rs::vector_literal_tail_lengths_are_packed_numerals`; bench family `conv/vec-literal`, the scaling datum — fuel does not see the difference (the repeated work was the element type's forcing and weakening, not counted steps), so the bench is the only linearity gate; it needs a desktop `scripts/bench --save` to enter the committed baseline. On furnace, `--quick`, same instance, old rule → new: 32 elements 3.49 ms → 0.30 ms, 512 elements 931 ms → 4.9 ms; slope ≈2 → ≈1.

## Residue
- The 27 mutations are still 27 modules; whether one per field family is the same evidence is a separate, now minor, trim.
- `byte_chain` remains for the lookups (each byte lookup re-runs the fold from the front); whether the literal form is now cheap enough to replace it is unmeasured.
- A `Vec` reached only by unfolding (an `El ⌜TmVec⌝` root, a definition that unfolds to a `Vec`) still takes the reductions at that one step; every level below is caught.

## What it assumes from elsewhere
- **[[kernel-failed-conversion-cost]]** owns the refused-conversion path. Assumed here: nothing any more — its 2026-09-11 log line naming this test as a customer datum is retracted there.
- **[[parallel-kernel-gate]]** owns the gate. Assumed here: that a one-theorem module cannot benefit from it, which is still true and still not the lever.

## Log
- 2026-09-11: Filed as a test-shape question (27 refusals at ~3 s per conversion).
- 2026-09-11: Measured; premise retracted, defect found and fixed as above. Numbers in the body.
- 2026-09-11: LANDED. Full `scripts/test` on furnace: 2582 passed, 0 failed, 5 ignored. `elf_header_mutations_are_rejected_by_heather` alone: 88 s → 7.5 s (library load included). Closing; the residue above is minor and has no owner it needs.

---
title: The x86 memory contract stated once: Loan, WroteIn, Injected and Sub, with the older tiers as instances
status: closed
labels: [native,x86,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Stage 1 of `docs/language/ownership-design.md` §17.5: the x86 memory contract stated once. Today it is in tiers that grew one at a time, each derived from the next (§17.1): `Stack::Unchanged` and `CalleeKeeps`; `Wrote`, `Stable`, `Through`, `Lends`, `Site::Calls`, `Framed`; `WroteIn`, `StableIn`, `Lending`, `InMemory`, `Trail`, `Trailed`, `Site::CallsOver`; `Site::CallsLent`; `Views`, `Viewed`, `Loan::view`, `Loan::onto`, `Lendable`; and experiment three's `Injected`, `Carved`, `Loan::carve`, `wrote_in_parents`, of which `Carved` is `Viewed` and `Loan::carve` is `Loan::view`.

## Scope

- **One module**, the memory contract, exporting: `Loan` and its laws, as built; `WroteIn` with reflexivity, transitivity, deepening and widening, and `Stable` with the frame rule; `Injected` (a heap of bytes with a shadow of references, into machine memory; `lib/native/reference_cells/reference_cells_x86.hthr` has the experiment's) with one lemma per memory operation at every width the machine has, and its stability under an own store; `Sub` (a part of a span: the one record that `Viewed` and `Carved` both are) with `Loan::sub` and `WroteIn::up`. The heap canonical: the bytes under an entry are zero.
- **The older tiers become instances**: `Wrote`, `Unchanged`, `CalleeKeeps`, `Framed`, `Site::Calls` are `WroteIn` at no spans; `Lends`, `LentAll`, `InMemory`, `Trail`, `Trailed` and their stability lemmas are `Injected` at an empty shadow and its lemmas; `Viewed`, `Loan::view`, `Loan::onto`, `wrote_in_view`, `Carved`, `Loan::carve`, `wrote_in_parents` are `Sub`. Each old name survives only as an abbreviation with a one-line derivation, for the existing lowering to cite until stage 3 deletes it. No statement is left with two independent proofs.
- **`Site::Meets`** (§17.2) is stated here as a definition, with the probe that the existing `Site::CallsLent` at one lending implies it at an empty shadow. Its use is stage 2's.
- `x86_64_views` and the experiment's `reference_cells_x86`/`_bridges` lemmas that restate these are folded in; the experiment's toy language and its program stay until stage 2 replaces them.

## Done when

The contract module and the abbreviations pass the suite with every existing certificate unchanged (`scripts/linked --check`, the native gates), and the log lists, for each old name, the one line it now is.

## What it assumes from elsewhere

- **[[ownership-reference-cells-spike]]** (closed) gives `Injected`, the shadow and the operation lemmas for one width.
- **[[bytes-level-language]]** owns what cites `Site::Meets`.

## Log

- 2026-11-25: Built (stage 1). One module, `lib/std/arch/x86_64/x86_64_memory_contract.hthr`; the older names live in `x86_64_memory_tiers.hthr` as instances, for the lowering to cite until stage 3 deletes both it and them. `x86_64_lending.hthr` and `x86_64_views.hthr` are deleted; their tests are `lib/_tests/std/arch/x86_64/x86_64_memory_contract_tests.hthr` and `x86_64_memory_tiers_tests.hthr`.

  **What the contract exports.** `Spans`, `Spans::byte`, `Spans::none`, `Loan` (laws as built), `Loan::canonical_at`, `Stack::loan_none`; `Stack::Put`, `Stores`, `WroteIn` with `wrote_in_refl/trans/word/store` and its order in one lemma, `Stack::wrote_in_widen` over `Spans::Within` (`within_self`, `none_within`, `within_none`); `Stack::StableIn`, `wrote_in_frame`, `stable_in_and/given/none`; what a span reads (`readable_at`, `Loan::own_reads`, `stable_span`, `store_reads`, `store_keeps`, `readable_window`, `readable_put_window`) and what a caller keeps (`Stack::UnchangedTo`, `Loan::stable_word/stable_resident/stable_reads/unwritten_reads/unchanged/resident`); `Sub` with `Sub::byte`, `Sub::within`, `Stack::wrote_in_up` (the issue's `WroteIn::up`: `WroteIn` is a method of `Stack`, so a theorem cannot attach to it), `Loan::sub`, `Sub::same`, `Loan::sub_outside/sub_unwritten_reads/sub_written_reads/sub_windows_reads`, `SubCovers`; `Loc`, `Pointer` (the shadow entry; `Entry` clashes with `rt_lower`), `Heap { bytes, shadow, undefined }`, `Heap::fits/plain/store/store_word/store_ref/byte/dword/word/Canonical`, `canonical_store`, `canonical_store_ref`; `Injected` with `Loan::store_injected` (any width), `store_word_injected`, `store_ref_injected` (derived from the word store), `Injected::reads` (any width) and its cases `byte_read`, `dword_read`, `word_read`, `ref_read`, `Loan::injected_own`, `Loan::stable_injected`, `Injected::same_bytes`, `Injected::undefined_change`; the System V definitions moved in from FunctionIR (`argument_registers`, `ArgsIn`, `Stack::Passes`, `Stack::Passed`, `callee_kept`, `answer_registers`); `Returned` and `Site::Meets` (provisional: the answering clause only), with the probe `calls_lent_meets` (`Site::CallsLent` at one lending gives it at an empty shadow).

  **Choices.** The canonical heap is in: a reference store zeroes its eight bytes (so it is a word store plus a pointer and its injection lemma is the word store's), and `Heap::Canonical` with its preservation lemmas sits beside `Injected`, not in it; no operation lemma carries it. Undefined bytes (the coordinator's addition) are a per-byte set, cleared by a store over its window, so no range splits. `Sub`'s place equation holds where a piece has a byte (the callee's buffers over views place an empty buffer anywhere), so `Loan::sub` takes the pieces' canonical bound. An eight-byte word stored exactly over a pointer replaces it, as in the experiment. `Stack::Own` and `Stack::Stable` stay in `x86_64_stack` (the stack's own vocabulary; `x86_64_stack_runs` states a frame's saves with `Stable`), and `StableIn` is `Stable` and the lent-store half. `read_word_agree` moved to `x86_64_data_read`.

  **Old name → the one line it now is** (all in `x86_64_memory_tiers` unless said):

  | Old name | Now |
  |---|---|
  | `Stack::Wrote` | `stack.WroteIn(i, Spans::none(), …)` |
  | `wrote_refl`, `wrote_trans`, `wrote_store` | `wrote_in_refl`, `wrote_in_trans`, `wrote_in_word` at `Spans::none()` |
  | `wrote_then` | `wrote_trans` of `wrote_store` (as before) |
  | `wrote_deeper` | `wrote_in_widen(d, i, le, none, none, within_self)` |
  | `wrote_frame` | `wrote_in_frame` at `Spans::none()` with `stable_in_none` |
  | `Stack::Unchanged` | `stack.UnchangedTo(from, stack.size, …)` |
  | `unchanged_refl/trans/above`, `store_below`, `wrote_unchanged`, `wrote_resident` | kept derivations (frame rule at `stable_word`/`stable_resident`; laws of the relation) |
  | `Through`, `stable_through`, `through_*`, `Lends`, `lends_*`, `lent_four` | unchanged definitions over `Wrote`; citations of the above |
  | `lent_address` | `readable_at(…).right` |
  | `wrote_in_own` | `wrote_in_widen(i, i, _, none, spans, none_within)` |
  | `wrote_in_put` | `wrote_in_store` at `[byte]` |
  | `wrote_in_deeper` | `wrote_in_widen(d, i, le, spans, spans, within_self)` |
  | `wrote_in_wider` | `wrote_in_up` at `Sub::fewer` |
  | `wrote_in_none` | `wrote_in_widen(i, i, _, spans, none, within_none)` |
  | `Loan::put_reads` | `store_reads` at `[byte]`, `put_window_cons` + `put_window_nil` |
  | `Loan::put_keeps` | `store_keeps` at `[byte]` |
  | `Loan::narrow` | `loan.sub(…, Sub::fewer(…), loan.canonical)` |
  | `Loan::wrote_reads`, `Loan::lends` | frame rule / `stable_through` at `stable_span` (as before) |
  | `Viewed` | record kept; `Viewed::sub` makes it a `Sub` |
  | `Loan::view` | `loan.sub(views.spans(spans), viewed.sub(), canonical_at)` |
  | `Stack::wrote_in_view` | `wrote_in_up` at `viewed.sub()` |
  | `view_outside`, `view_unwritten_reads`, `view_written_reads`, `view_windows_reads` | `sub_outside`, `sub_unwritten_reads`, `sub_written_reads`, `sub_windows_reads` at `viewed.sub()` |
  | `ViewCovers` | `SubCovers` at the views |
  | `Loan::onto` | `loan.sub(other, Sub::same(…), canonical)` |
  | `Stack::wrote_in_onto` | `wrote_in_up` at `Sub::same(…)` |
  | `Carved` (toy) | record kept; `Carved::sub` |
  | `Loan::carve`, `Stack::wrote_in_parents` (toy) | `loan.sub` at `carved.sub()`, `wrote_in_up` at it |
  | toy `Injected`, `store_word_injected`, `store_ref_injected`, `word_read`, `ref_read`, `byte_read`, `Injected::canonical` | the contract's (`Loan::canonical_at` for the last) |
  | `in_memory_injected`, `injected_in_memory`, `Injected::same_bytes` (bridges) | moved: the first two to `function_ir_lower_calls` beside `InMemory`, the last to the contract |
  | `Stack::in_memory_span` | `store_injected` at `Heap::of(now)` through the two bridges |
  | `Stack::in_memory_put` | `in_memory_span` at `[byte]` and `in_memory_same` |
  | `Stack::stable_in_memory` | `stable_injected` through the bridges |
  | `in_memory_word_stored` (bridges) | `in_memory_span` at `word_bytes(word)` |
  | `CalleeKeeps`, `Site::Calls`, `Framed`, `Trail`, `Trailed`, `LentAll`, `InMemory`, `LentOver`, `CalledOver`, `AnsweredOver`, `Site::CallsOver`, `Site::CallsLent` | definitions unchanged in `function_ir_lower_calls`, over `Wrote`/`WroteIn`/`InMemory`, now the contract's instances; `callee_keeps` stays the frame rule's |

  **Did not become an instance as a statement.** `Viewed` and `Carved` stay records (their constructors are written by `Lendable::parts`, the tests and the toy), each with a `fn …::sub` into `Sub`; their lemmas are `Sub`'s. `Stack::InMemory` keeps its statement (callers destructure it) and is `Injected` at an empty shadow both ways through a loan (`injected_in_memory` needs the loan's canonical bound). The per-span `Readable` lemmas (`store_reads`, `store_keeps`, `own_reads`, `stable_reads`, `unwritten_reads`) are a second, per-span way of saying what a store leaves beside `Injected`'s per-heap one; nothing proves the same statement twice, but the two levels stand (filed as [[x86-memory-contract-readable-spans]]). The toy's `load_byte_refused` now names `touched(…, 1)` where it named `covered`, a byte load being `plain` at width one.

  **Cost** (fresh cache, the closure of `reference_cells_bridges`, kernel steps): `function_ir_lower_calls` 10,377,576 → 10,382,231 (+0.04%), `function_ir_lower_views` 779,755 → 780,600, `x86_64_byte_memory` 748,746 → 744,874; the memory tiers (`x86_64_stack`, `_lending`, `_views`, the toy's three) 2.91M → 2.60M (`x86_64_stack`, `_memory_contract`, `_memory_tiers`, the toy's three), with the contract adding the widths, undefined bytes, the canonical heap and `Site::Meets`. Wall time per item moved by noise only (equal counts).

  **Verified.** The 108 modules importing the touched ones checked one by one (`heather check --cache --expectations`, capped); `scripts/linked --check`: 17 exports compiled with checked certificates, every assembly file unchanged. Suite: see the next entry.
- 2026-11-25: Two additions after the coordinator's notes, then the final verification.

  - **Undefined bytes** (per byte, beside the shadow): a byte is plain, part of a reference, or undefined. `Injected` constrains only defined bytes; `Injected::undefined_change` keeps it under any memory change at undefined, uncovered bytes (a failed `read` that left junk); a store defines its window, so no range splits; `Heap::plain` refuses an undefined byte; `Heap::Canonical` includes zero under undefined bytes.
  - **The heap as lists**: `Heap { blocks: List<List<BitVec(8)>>, shadow, flags: List<List<Bool>> }`, read only through `Heap::bytes` and `Heap::undefined`; a store updates the lists where it layered a closure per store. `Injected`'s and the operation lemmas' statements did not change (their proofs go through `Heap::store_bytes`, `Heap::store_undefined`). `Heap::of(buffers)` is `Heap(buffers, [], [])`, so `Heap::of_store` is `refl`. Kernel steps for a run of k load-then-store steps, k = 8, 16, 32, 64: 2,866 / 6,258 / 15,346 / 42,738 as closures (quadratic), 2,838 / 5,398 / 10,518 / 20,758 as lists (linear). The internal helpers `Heap::store_len`, `store_outside`, `canonical_kept`, `canonical_store` now take `inside` (the store's first byte is in its block), which every caller had.

  **Verified on the final tree**: `scripts/linked --check`, 17 exports compiled with checked certificates, every assembly file unchanged; `HEATHER_PR_NATIVE=all scripts/test --pr`: `== suite: 3517 passed, 0 failed, 2 ignored ==`.

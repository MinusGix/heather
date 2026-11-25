---
title: References held in memory down to x86: a shadow beside the bytes and an injection of blocks
status: open
labels: [ownership,native,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The third experiment of `docs/language/ownership-design.md` (§16, the riskiest package's earliest test): references held in memory, down to x86. §15.7 settles that a reference stays a reference to the machine, crossing by an injection of blocks; §16 proposes making that change additively, with a shadow beside the bytes. Whether that works is unknown until something small is proved through.

## Scope

A toy language at the bytes level, in its own module:

- **Values** are words and references (a block and an offset). **Memory** is blocks of bytes with a shadow: which eight-byte slots of which block hold a reference, and to what.
- **Operations**: store a word, load a word, store a reference into a slot, load a reference from a slot, load a byte through a reference.
- **Its meaning** is unchanged by renaming blocks (state and prove that: no operation observes a block's address).
- **A lowering to x86** and its theorem, by an **injection**: each block's bytes are at its address off the shadow, a shadowed slot holds its target's address, blocks are disjoint; the injection is preserved by a run. Cite what the machine side has: `Loan`, `Spans` (`lib/std/arch/x86_64/x86_64_lending.hthr`), `DataRegion::loan` and the span lemmas of `x86_64_byte_memory.hthr`.
- **One program**: store a reference in a slot, load it back, read a byte through it; compiled, with its theorem. Controls: a byte load of a shadowed slot is refused or owes a fact; two blocks placed overlapping break the injection (a `¬` theorem).

## What it must find out

1. **Is the shadow additive?** Does a memory with an empty shadow reduce to the bytes-only statements that exist, so existing theorems are the special case?
2. **Does the register invariant split by kind?** Read the central invariant of `lib/native/function_ir/function_ir_lower.hthr` and `function_ir_lower_calls.hthr` ("a register holds the valuation's word") and say, from what the toy's proof needed, what it becomes for a reference and how much of those two modules it would touch. This is a reading and a judgment, not a change to them.
3. **What `Loan` needs** to cover a block obtained after entry (a new span carved from a supply).
4. **What a byte copy of a record holding references needs** (a typed copy, or fragments).

## Done when

The toy's theorem is proved through to x86 for the one program, the controls are theorems or refusals, and the log answers the four questions with evidence.

## What it assumes from elsewhere

- **[[ownership-discipline-over-code]]** owns the design this tests. It changes nothing in `lib/native/function_ir` or `lib/std/arch/x86_64` beyond lemmas added under new names.

## Log

- 2026-11-25: Round 1 (branch `claude/ownership-reference-cells`). **The toy is proved through to x86 for the one program, the controls are theorems, and the four questions are answered below.** Modules: `lib/native/reference_cells/{reference_cells, reference_cells_x86, reference_cells_bridges}.hthr`, probes `lib/_tests/native/reference_cells/reference_cells_tests.hthr`. Nothing in `lib/native/function_ir` or `lib/std/arch/x86_64` was changed; no existing statement had to change for the toy to go through.

  **What is proved.**
  - The level (`reference_cells`): values are words and `Ref(Loc(block, offset))`; a heap is bytes per block (`Heap::of(buffers)` is FunctionIR's `Buffers()` with an empty shadow) and a shadow of `Entry(block, at, target)`, eight bytes each. Five operations, each partial: a byte or word load of a shadowed byte, a reference load where no entry is, and a store that *cuts* an entry have no step. `run_renames`: a run of a renamed state is the renamed run; `run_words_alike`: a word computed is the same under any renaming of blocks.
  - The injection (`reference_cells_x86`, `Injected`): blocks as long as their spans; a byte no entry covers reads its byte; an entry's eight bytes read its target's address. Kept by each store from a `Loan`'s `stored` and `apart` laws alone (`Loan::store_word_injected`, `Loan::store_ref_injected`); read by each load (`Injected::word_read`, `ref_read`, `byte_read`).
  - The lowering: one instruction per operation, the same for a word and a reference (`MOV [base], src` for both stores, `MOV r, [base]` for both loads, `MOVZX` for the byte). `Loan::op_runs`: from a state where the registers hold the lowered values and the heap is injected, if the operation steps then the instruction's normal step as x86_64 states it exists (`WordLoadStep`, `ByteLoadStep`, `word_store_after` with its writable span) and ends in such a state. `Loan::lowered_runs` chains it over a program; `Loan::program_lowered` with the lowering's check.
  - The program (`program`: `StoreRef(0, 1); LoadRef(2, 0); LoadByte(3, 2)`): `program_lowers` and `program_code` (`MOV [RDI], RSI; MOV RAX, [RDI]; MOVZX RCX, byte [RAX]`) by evaluation, `Loan::program_runs` its theorem; probes run it on a heap (`program_reads_nine`).
  - Controls: `load_byte_refused` (a byte load of a byte an entry covers has no step) and the probe `byte_of_reference_refused` (the reference aims into its own eight bytes); `overlap_not_injected` (two blocks whose spans share a byte, different there, are injected by no memory) and its instance `overlapping_not_injected`. Refusals beside positive twins: `word_of_reference_refused`, `reference_of_bytes_refused`, `cut_refused` / `store_beside_kept`, `whole_store_replaces` / `replaced_reference_gone`.

  **Q1, is the shadow additive: yes for the memory relation, proved both ways.** `in_memory_injected` and `injected_in_memory`: an empty-shadow heap injected under a loan *is* `Stack::InMemory` (function_ir_lower_calls). `store_word_of`: the toy's word store on buffers is `store_span`, block for block. `in_memory_word_stored`: the toy's store theorem at an empty shadow yields `Stack::in_memory_span`'s conclusion for a word. Not free: the *file type* of the call contracts. `Effects()` relates `Buffers()` before and after a call in about 90 places across ten `function_ir` modules (33 in `function_ir_lower_calls`); a program that keeps a reference in a block a callee is lent needs that file to carry the shadow. Filed as [[reference-cells-call-contracts]].

  **Q2, does the register invariant split by kind: no, and it need not.** The toy's invariant is one statement for both kinds, `read_gpr(reg(x)) = values(x).lower(spans)`; the kind lives in `Value::lower` (a reference lowers to its target's address). `held_word_rep` and `registers_represent` (reference_cells_bridges): that invariant *is* `Held::Rep` at kind `Word` over the valuation lowered through the injection (`lowered_values`). So `Kind`, `Held`, `File::Represents` and the theorems stated over it keep their statements: of `function_ir_lower`'s 148 theorems, the 90 stated over `Represents`/`Keeps`/`MayKeep`/`Guards` are instantiated at the lowered valuation unchanged (e.g. `File::represents_write`, `File::binary_keeps`, `File::compare_keeps`, `File::place_keeps`), and so are the 47 such in `function_ir_lower_calls` (`EmitsIn`, `load_emits`'s register half). The existing buffer homes are already this case: `Lent::Holds` says `values(64, base) = address_of(addresses, b)`, a reference's `Rep` stated as a fact about the valuation; what changes is that the address leaves the meaning's valuation and appears only in the lowered one. What the change does touch: (a) FunctionIR's ids must be typed word or reference (a second valuation, overridden by addresses in the lowered one); (b) a per-node check that no word node reads a reference id, since only then does a node's equation transfer to the lowered valuation (this is what `placeless` becomes: local, no loop fixpoint; its meaning-level statement is `run_renames`); (c) new nodes and their emit theorems beside `load_emits`; (d) the 82 `function_ir_lower_calls` theorems over `InMemory`/`Trail`/`Lending`/`Buffers()` (e.g. `Stack::in_memory_put`, `Stack::trail_span`, `Stack::CalledOver`, `Site::CallsLent`), which are Q1's and Q3's, not the register invariant's. A new case beside the old, at the valuation; not a change to the statement every proof goes through. Filed as [[reference-cells-id-kinds]].

  **Q3, what `Loan` needs for a block carved after entry: nothing new.** `Loan::carve`: spans that are pieces of a loan's spans (each inside its parent, a written piece of a written parent and apart from every other piece of it, `Carved`) are a `Loan` under the same stack and `top`. `Stack::wrote_in_parents`: every store into a piece is one into its parent, so the footprint stays the entry lending's. What does change is the threading: `function_ir_lower_calls` states a body's memory against one `Lending` fixed for the program, and across an allocation the current pieces must be carried in the invariant instead. Filed as [[reference-cells-lending-per-state]].

  **Q4, a byte copy of a record holding references: a typed copy, no fragments, wherever the layout is known.** A reference cell copied by `LoadRef`/`StoreRef` is the same pair of `MOV`s a word copy emits (probe `typed_copy_reads_nine`, and `copy_lowers`). A byte loop over a reference's bytes has no meaning (`byte_of_reference_refused`). The proof forced one more rule: a store that cuts an entry must be refused (`cut_refused`), because the bytes left under the cut entry hold part of an address the meaning cannot name; `Loan::store_word_injected` needs the cleared entries to lie wholly under the store. Fragments would be needed only to write a copy of unknown layout as a loop in the meaning; the lean for a generic move is a primitive range copy that moves whole entries. Filed as [[reference-cells-range-copy]].

  **What surprised.** (1) The cost: the machine module's declarations check in about a second in all; the costliest, `Loan::stored_block_byte`, about 0.2 s. The toy states its steps over x86_64's step records directly, at neutral parameters, through stage theorems; it does not go through `Site`/`Prog`/fetch, which are unchanged by references (the same instructions as `load_emits` already runs). (2) The register side, named the riskiest, was the cheapest: the kind never reached the register file. (3) The cut rule was not in the design; it came out of the store proof, and is the bytes-level face of question 4. (4) `ByteLoadStep`'s canonical premise is in `drop_low` form where `WordLoadStep`'s is a `toNat` bound (bridged by `BitVec::drop_low_zero_of_lt`); harmless.

  **Where it stops.** The theorem is over the instructions' normal steps, not fetched code at labels in a frame; that plumbing is the real lowering's and is the same for these instructions. The toy has no allocation (Q3 is answered by `Loan::carve` and `wrote_in_parents`, not by a program that allocates) and no call. Verification: each module checked cold with `--limits dev`; `scripts/test --pr` recorded in the next entry.

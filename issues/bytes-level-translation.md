---
title: FunctionIR programs translated to the bytes level, and crates/linked's exports compiled both ways
status: open
labels: [native,function-ir,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-26
---

Stage 2 of `docs/language/ownership-design.md` §17.5, its last part: every FunctionIR program translated into the bytes level, and the evidence that the new layer can replace the old in one move (stage 3): every row of `crates/linked`'s exports compiled both ways gives the same assembly, or a reviewed difference.

## Scope

- **The translation**, a Heather function from a FunctionIR `Function` list and its buffer counts to a `bytes_level::Program`. Buffer `k` becomes a reference parameter and a length word (`2k`, `2k + 1`, as `Function.lent` already passes them). `BufferLoad`/`WideLoad` become an `Offset` and a `Load`. `BufferStore`/`WideStore` become an `Offset` and a `Store`. `Lend` becomes the views' `Offset`s and a `Call` on references and lengths. `Call` and `Loop` keep their shape, and word nodes are wrapped in `Compute`. A `Fixed` span is a reference whose length is the routine's constant.
- **Where the meanings differ, said once.** FunctionIR's loads read zero and its stores do nothing past a buffer's end; at the bytes level a load or a store there has no answer. A byte the old program reads past an end therefore becomes a comparison and a branch in the translation, as the old lowering already guards each such access with a comparison. A program whose stores land past an end is refused, not silently given a meaning.
- **The theorem.** Run on the heap that is the buffers (`Heap::of`, an empty shadow, `written` from the lending's marks), every `Done` of the translated program, at any fuel, is the old program's run (`function_ir_run`'s writers or the state evaluation) with the buffers read back from the answer's heap. This is stated once, over programs, and not per export.
- **The comparison.** For each row of `crates/linked`'s exports (`scripts/linked`), compile the old way and through the translation and the new lowering ([[bytes-level-lowering]]), and compare the assembly. Where they differ, the difference is listed and reviewed (a placement, a guard), and either fixed or accepted with its reason in the log.

## Done when

The translation and its theorem pass the library gate; the comparison runs over every export row and its outcome is in the log, with the differences reviewed.

## What it assumes from elsewhere

- **[[bytes-level-language]]** owns the target language and `run`.
- **[[bytes-level-lowering]]** owns the new lowering the comparison compiles through.

## Log

- 2026-11-26, item 1: **the survey.** Each row's forms were counted by evaluating a census over the program compile-x86 lowers: the `_cut` program after the optimizer, read from the row's kept certificate (word-only rows lower `_program` directly). The certificates were written by `scripts/bytes-level-compare --compile-only`.

  | Row | Forms in the lowered program |
  |---|---|
  | sha512_t1, _t2, _next | word nodes, `Call` (3 functions, no buffers) |
  | sha256_t1, _t2, _next | word nodes, `Resize` (1 function) |
  | sha256_compress, _update, _finish | `BufferLoad` 8–10, `BufferStore` 11–14, `WideLoad(4)` 19–20, `WideStore(4)` 8–10, `ByteSwap` ~20, ~130 conditionals, 61–86 calls to lent callees, 9–10 bounded loops, 25–31 lent functions |
  | sha256_init | `BufferStore` 8, `WideStore(4)` 1, `ByteSwap` 1, 11 calls |
  | count_newlines, raise_span, list_raise_letters, copy_span | `BufferLoad` 2, `BufferStore` 0–2, one bounded loop, at most one call |
  | copy_window | as copy_span, and the exports' only `Lend` (two views, one written) |
  | scan_token (scan_step, scan_accept, scan_begin as entries) | `BufferLoad` 2, ~480 comparisons, ~400 conditionals, 36 calls, one loop |
  | scan_tokens | `BufferLoad` 2, `BufferStore` 8, `WideStore(4)` 1, `ByteSwap` 1, ~400 conditionals, 51 calls, two loops |

  No export uses wide accesses at 2 or 8 bytes (or any other width), `TableRead`, a `Fixed` span, levels, or `also`.

  The native gates add:
  - `also`: enum_fields, enum_payload, narrow_fields, two_words.
  - A `Fixed` span, through compile-x86's sret wrapper: three_words.
  - Levels: recursion, native_program's `LEVELS`, native_recursion (with the run-time exit 139).
  - Buffer loads and stores, bounded loops and lent calls: binary_search, sort, utf8.

  native_cat and native_tools compile through the program compiler (`native_compile*`), not FunctionIR.

  Status of each form at the bytes level:
  - Word nodes are `Compute` and lowered by the same `lower_nodes`.
  - A byte load or `WideLoad(4)` becomes `Offset` and `Load(1 | 4)`. It lowers to `ADD` then `MOVZX` or `MOV r32`, the shape the old load already emits.
  - A byte store or `WideStore(4)` becomes `Offset`, `Store` and a reload `Load`, which is the old node's output.
  - Two-byte accesses are refused by the lowering ([[bytes-level-copy-and-halfwords]]). No export uses them.
  - `Call` lowers, recursion included.
  - `Lend` becomes the views' `Offset`s and a `Call`. The old meaning clips a view at its buffer's end, so the translation states the clipped length.
  - A bounded loop becomes a plain loop with a counter, an exhausted bit, and a bound-zero branch before it.
  - `also` and `Fixed` exist in the language (a results list; a reference and a constant length).
  - Levels have no counterpart. The old meaning answers zero past the last level, while the translated meaning recurses on. The out-of-room exit has no meaning ([[bytes-level-lowering-recursion]]).
  - `TableRead` is refused by `lower_nodes` on both paths.
- 2026-11-26, item 2: **the translation** (`lib/native/bytes_level/bytes_level_from_function_ir.hthr`).
  - Its shape:
    - `translate_program` numbers routines from the first; FunctionIR lists its functions last first.
    - Buffer `k` is the reference parameter `2k` and the length word `2k + 1`; a `Fixed` span is parameter 0 and the port the body sets.
    - A scope names a buffer by its home, as the old lowering does: `Lent`, `loop_carried` inside a loop, `StructuredRegion::lends` after one.
  - Nodes:
    - A byte load is `Offset` and `Load(1)`.
    - A byte store is `Offset`, `Store(1)`, and `Load(1)` for the old output.
    - A wide access at 1, 2, 4 or 8 bytes is `Offset` and `Load`/`Store`. The store is reloaded only where the function reads its output; the old lowering leaves that output unheld.
    - Word nodes are `Compute`.
  - Calls and lends:
    - A call is a call on the values.
    - A lend is the views' `Offset`s and lengths, then the call.
  - A bounded loop is the plain loop with the counter and an exhausted flag as the state's last two elements.
    - The pass's tail branches on the old exit bit: counter 0 and flag 0, or counter `+ (2^64 - 1)` and flag 1. Then the test is `counter = 0`; after the loop, `exhausted = (flag = 1)`.
    - The exit bit is only branched on, because the old planner may have folded its comparison into the test. A materialised comparison needs two registers the old placement does not leave (count_newlines has none spare).
    - Before the loop, a bound-zero branch, skipped where the path knows the bound is a nonzero constant (every export's loop: `2^64 - 1`).
  - Where the meanings differ (`Scope::memory`, using the old lowering's own `File::bounded`/`span_bounded` over the same `Known`s):
    - A byte load not known inside becomes a comparison and a branch (zero past the end).
    - A store or wide load not known inside is refused.
    - A lend whose views are not known lendable and apart is refused.
  - Also refused, as the old lowering refuses them:
    - a function with levels;
    - a call of a function not below its caller, which the old meaning answers with zero;
    - a lent callee not given the caller's homes first (`calls_below`, `args_lend`).
  - Found by the comparison: the optimizer writes a decided comparison's bit right after the comparison (one id bound twice). The translation drops a pure node a later node of its leaf rebinds before anything reads it (`rebound`). That is exact in meaning, and its facts are still gathered.
  - Probes (`lib/_tests/native/bytes_level/bytes_level_from_function_ir_tests.hthr`): each run is two closed verdicts, the new answer and the old (`program_run`), and their agreement.
    - The exports' own source programs: `count_newlines`, also past its end; `raise_span`'s word and the span after it; `copy_window`'s lend.
    - One per form: a guarded load inside and past the end; a store and its output; a wide load and store; a loop that runs out (with its exhausted bit), one of no passes, one that exits, one that exits on its last allowed pass.
    - Controls: a store not known inside, refused; a wide load not known whole, refused; a leveled function, refused.
    - The comparison on a word function lowered both ways: the same 7 bytes.
  - Verification: `scripts/fmt --check` and `scripts/lib-closures` clean; `scripts/linked --check` unchanged; `HEATHER_PR_NATIVE=all scripts/test --pr`: `== suite: 4139 passed, 0 failed, 3 ignored ==`. That run predates two changes: the drop restricted to pure nodes, and the call checks. The modules and probes were re-checked after them, and the final verification re-runs the suite.
- 2026-11-26, item 4: **the comparison** (`scripts/bytes-level-compare`; `--gates` for the gates' programs; no test lane runs it, since it compiles every row).
  - How it works:
    - It compiles each row the old way with `compile-x86` and keeps the certificate under the key `scripts/linked` uses.
    - It reads off the certificate what the lowering was given (`_cut_program` or `_program`, the counts, the planner's `_placement`) and the old `_code` (`scripts/bytes-level-compare-defs.py`).
    - It evaluates `compare_report` (`bytes_level_compare`): the translation, the placement translated in step with it, `Program::lower`, and the bytes of both codes.
    - Both codes are disassembled and diffed routine by routine, call and jump displacements aside (`scripts/bytes-level-compare-diff.py`, writing `old.s`, `new.s`, `diff.txt` per row).
  - Its own checks:
    - The evaluated old bytes equal the published `.s`, for every row that lowered.
    - `asm_code` re-measures everything before each item, which ran out of memory on scan_token, so the comparison assembles in one pass (`prog_bytes`).
  - Exports:

    | Row | Outcome |
    |---|---|
    | sha512_t1, _t2, _next; sha256_t1, _t2, _next | same bytes (223, 145, 182, 133, 100, 137) |
    | count_newlines | +8 bytes, only its loop's routine |
    | raise_span, list_raise_letters | +8, only the loop's routine |
    | copy_span | +12, the loop's routine |
    | copy_window | +12, the loop's routine; the lend's routine has the same instructions |
    | scan_token | +8, only routine 36 (its loop) of 39 |
    | sha256_compress | refused: `ByteSwap(32)` of a `Load(4)` (routine 6) |
    | sha256_init, _update, _finish; scan_tokens | refused: `Store(4)` of a `ByteSwap(32)` (routine 1; scan_tokens routine 41) |

  - Gates:

    | Program | Outcome |
    |---|---|
    | two_words add_wide, enum_fields signal (words past the first) | same bytes |
    | three_words stats (a structure through memory: `Fixed`, eight-byte stores) | same bytes |
    | branches nested_true | same bytes |
    | binary-search lower_bound | +12, the loop's routine |
    | utf8 utf8_valid_up_to | +8, the loop's routine |
    | sort sort_in_place | +8 and +16, its two loop routines |
    | recursion rsum | refused by the translation (levels) |

  - The differences, reviewed. Every routine without a bounded loop is byte-identical, call displacements aside. Each difference has one of four causes:
    1. **The bounded loop** (every loop routine). The bytes level has only the plain loop, so the counter and an exhausted flag are the state's last two elements, in the old placement's counter and flag registers.
       - Old: `TEST counter; JE` at the head of each pass, `MOV flag, 0/1` on leaving.
       - New:
         - one `MOV flag, bound` at entry;
         - a tail branch on the exit bit (`MOV counter, 0; MOV flag, 0` or `ADD counter, -1; MOV flag, 1`), then `CMP counter, 0; JNE`;
         - after the loop, `CMP flag, 1` where the old code tested the flag;
         - a jump to a jump at the tail's join.
       - Net +8 bytes, +12 where the registers take REX prefixes. Accepted for stage 2, as a temporary cost of translating bounded loops, removed when loops are reflected directly. The coordinator ruled out a counted loop at the bytes level, since the old counter is the old meaning's fuel; the per-pass numbers are item 5's entry 2.
    2. **A reference's copy** (sort routine 2: an `ADD r, 0`). The optimizer leaves a dead `Move` of the span's reference. The bytes level has no reference move, so the translation copies it as an `Offset` of a folded zero. Accepted; a reference `Move` instruction would remove it.
    3. **Four-byte accesses' register kind** (the four sha256 rows and scan_tokens refused). `Program::lower` holds a `Load(4)` result as `Word` and takes a `Store(4)` value only as `Word`, where FunctionIR's wide forms use `Narrow(32)`. So a `ByteSwap(32)` after a dword load is refused, and so is a dword store of a `ByteSwap(32)`. Smallest programs:
       - `Leaf[Offset(t, r, i), Load(4, x, t), Compute(ByteSwap(32, y, x))]`
       - `Leaf[Compute(ByteSwap(32, y, x)), Offset(t, r, i), Store(4, t, y)]`
       Reported to the coordinator, not worked around.
    4. **Levels** (rsum): no counterpart at the bytes level.
  - The translation changes the comparison drove, each exact in meaning:
    - **A loop's pass read at an offset of its own**, past every id so far (`translate_region`'s `d`). FunctionIR runs each pass in its own valuation, and the optimizer's copies reuse a pass's ids after the loop (sort), which the bytes level's scope check refuses.
    - **A `Move` of a reference** copies the reference.
    - **A function's results typed by its scope**: the sret wrapper answers its reference.
    - **The bound-zero check skipped** where the bound is a known nonzero constant.
- 2026-11-26, item 3: **the theorem** (`lib/native/bytes_level/bytes_level_from_function_ir_sound.hthr`). It is stated once, over programs, as `translated_runs_as_old`. The premises:
  - `translate_program(functions) = Some(p)`;
  - every function fits (`ProgramFits`);
  - function `f` below the program's length;
  - arguments that agree with the old words (`ArgsAgree`: buffer `k` is a reference to block `k` from 0 and its length, then words);
  - a heap whose every block is its buffer.

  Its conclusion: every `Done` of `run(p, blocks, fuel, f, args, heap, io)` at any fuel has the words of `program_run(functions, buffers, f, words)` (its word, then its rest), and a heap whose blocks are the buffers that run left.
  - How it is proved, in stage lemmas:
    - The memory nodes: `byte_load_runs`, `byte_store_runs`.
    - A node keeps the relation and runs as the old node (`node_agrees`). The relation is `Agree` (old and new words equal on every non-reference id below the bound and not pending) and `HomesHeld` (each home's reference is its block from 0, and each block is its buffer).
    - A leaf (`leaf_runs_as_old`).
    - The bodies the translation joins (`seq_bodies_done`).
    - A call (`call_agrees`) and a branch (`branch_agrees`).
    - A region (`region_owes`).
    - A routine's entry and its `Done` (`entry_binds`, `function_owes`).
    - The program (`program_calls_agree`).
  - The induction is over the program's functions, not over fuel. A routine calls only below itself, so the last function's calls are answered by the theorem for the rest, at the fuel the call has left. No fuel argument is needed beyond `program_calls`'s own.
  - Not found from the design note:
    - Pending ids. The translation drops a pure node rebound before it is read (`rebound`, item 2), so the relation must exempt those ids until their second write. A leaf's ids are all written by its end, so nothing is pending between leaves.
    - A reference is never an old word. `Agree` holds only off the scope's references, and every premise that reads an id says it is a word id (`AllWords`, a condition's or a result's `mem_nat(id, refs) = False`).
  - **What it covers** (`RegionFits`, `FunctionFits`):
    - leaves of word nodes, byte loads known inside (no guard) and byte stores;
    - sequences, compositions and conditionals;
    - calls of one result to a function below, lent callees given the caller's homes;
    - functions of no levels, no `Fixed` span and one result.

    Of the exports, the six word-only rows fit: sha512_t1, _t2, _next and sha256_t1, _t2, _next. Of the gates, branches nested_true fits.
  - **What remains**, by form:
    1. **Bounded loops** (`RegionFits` is `False` at `Loop`). A pass runs at an id offset `d` of its own (item 4), so the relation needs a shifted `Agree` between the pass's valuation and the locals at `id + d`. It also needs an induction over passes matching `loop_pass_run` against the plain loop's fuel: the counter and flag elements, and the bound-zero branch. Every export with memory has a loop, so this is the next piece.
    2. **Lends.** A view is an `Offset` into the lender's block, so "each block is its buffer" breaks inside the callee. The relation has to become "each home's reference is its buffer's view": a base and a length within a block.
    3. **Wide accesses** (`is_wide` excluded). They need a wide `byte_load_runs`: the little-endian read of n bytes equals `Buffers`' wide read, at 1, 2, 4 and 8 bytes. Only `WideLoad(4)`/`WideStore(4)` are in exports, and those rows are refused by the lowering anyway (item 4, cause 3).
    4. **Guarded loads.** The comparison-and-branch form is excluded (`LeafOk` asks for one leaf). It needs `branch_agrees` with the guard's condition read from the bound's comparison.
    5. **`also` and ref results** (two_words, enum_fields, narrow_fields; three_words' sret).
    6. **Levels and the `Fixed` span** (recursion, native_program's `LEVELS`, native_recursion). Levels have no counterpart at the bytes level (item 1), so this is a stage-3 language question, not a proof.
    7. **No decider for `ProgramFits`.** It is a `Type` whose premises quantify over the translation's intermediate results. Applying the theorem to a row by `refl` needs a `Bool` check and its soundness. Without that, the coverage above is read off the forms, not checked per row.
  - Verification: the module checks in the library gate; `scripts/linked --check` unchanged.
- 2026-11-26, item 5: **what stage 3 still needs** (§17.8), with the coordinator's rulings.
  1. **An access names the view it uses** (ruled: the language's definition is too coarse). Today `Program::lower` holds a `Load(4)` result as `Word` and takes a `Store(4)` value only as `Word`. That refuses sha256_compress, _init, _update, _finish and scan_tokens: the hash's buffer rows and the lexer's whole-input row, the rows whose per-pass cost matters most.
     - The ruled definition: `Store` gains the width of the view it stores from, and `Load` the kind its output is held at.
     - It was not built in this round; the handoff is the next entry.
  2. **Bounded loops: a temporary cost of translating them, removed when loops are reflected directly** (ruled: no counted loop at the bytes level; the old counter is the old meaning's fuel). The cost is the same in every loop of every row that lowers, since each has the same shape (the old `TEST; JE` at the head, `MOV flag, 0/1` at the end):

     | Row | Loops | Bytes added | Per continuing pass |
     |---|---|---|---|
     | count_newlines | 1 | +8 | +1 MOV, +1 taken JMP |
     | raise_span, list_raise_letters | 1 | +8 | +1 MOV, +1 taken JMP |
     | copy_span, copy_window | 1 | +12 (REX) | +1 MOV, +1 taken JMP |
     | scan_token (routine 36) | 1 | +8 | +1 MOV, +1 taken JMP |
     | lower_bound; utf8_valid_up_to | 1; 1 | +12; +8 | +1 MOV, +1 taken JMP |
     | sort_in_place | 2 | +8, +16 (the +16 includes item 3's `ADD r, 0`) | +1 MOV, +1 taken JMP |
     | sha256 buffer rows, scan_tokens | 9–10; 2 | not measured: refused (1 above) | the same shape expected |

     - Per continuing pass, the old code runs 6 loop-control instructions: `TEST; JE` (not taken), `CMP; JNE`, `ADD counter, -1`, `JMP` head. The new code runs 7: `CMP; JNE`, `ADD`, `MOV flag, 1`, `CMP counter, 0; JNE`, then `JMP` head.
       - The head's `TEST; JE` becomes the tail's `CMP; JNE`: moved, not added.
       - The `MOV flag, 1` is the translation's. It records that the pass was a counted one, for the exhausted bit read after the loop.
       - The extra taken jump is the lowering's: the jump to a jump.
     - Once per loop: `MOV flag, bound` at entry. After the loop, `CMP flag, 1` replaces the old `MOVABS flag, 0/1` and `TEST flag`. The `MOVABS`es becoming 32-bit `MOV`s is why the net is +8 and not more.
  3. **The jump to a jump is the lowering's** (`plain_jumped`, bytes_level_lower). It lays a pass's end out as the test, `Jcc C`, the moves, `JMP J`, then `C:` the moves and `JMP H`. Where the moves are empty (every row here), `Jcc C` lands on a bare `JMP H`. A `Jcc H` there would remove one taken jump per pass and leave the per-pass count at the old 6. This is a lowering change, and `plain_done`'s proof is shaped around the layout; not made.
  4. **The dead reference `Move`** (sort routine 2, `ADD r, 0`). It is dead: nothing reads its output. The old placement gave it the source's register, so the old code has no instruction for it. Two ways out:
     - The translation could drop it, as it drops a rebound pure node: exact in meaning, with a placement stream that skips it.
     - A reference move in the language would lower to nothing in the same register.

     The drop is the smaller change, and no row needs a live reference move.
  5. **Levels and the out-of-room exit 139**: the coordinator's to design (room is a premise of the contract; the stop is defined). The translation refuses a leveled function with that reason (recursion, native_program's `LEVELS`, native_recursion).
  6. **A refusal report.** `Program::lower` answers `None` with no reason; `compile-x86`'s old refusal names the node, its place and the registers. Every finding here needed a hand diagnosis (`bytes_level_compare`'s `refused`/`invalid_path`).
  7. **The two scoping normalisations** the translation makes for what the old optimizer emits and the bytes level's scope check refuses (one binding per id per scope):
     - **The rebound drop**: a pure node whose id a later node of its leaf binds before anything reads it.
       - Counts: sha256_compress 60, _update 60, _finish 65, _init 3; scan_tokens 3; sort_in_place 2.
       - None in the other rows. It fires mostly in rows the lowering refuses, so its cost in bytes is unmeasured there; it emits nothing.
     - **The pass's id offset `d`**: every loop's pass is read at ids past every id so far.
       - It applies to every loop: 1 in each loop row, 9–10 in the sha256 buffer rows, 2 in scan_tokens and in sort.
       - It is needed where the optimizer's copies reuse a pass's ids after the loop, which is how it was found (sort). It costs nothing in code: ids are not registers.
  8. **Stores that reload.** Every byte store's reload in every row is dead (byte stores / dead reloads):
     - raise_span, list_raise_letters, copy_span, copy_window: 2/2 each;
     - sha256_compress 11/11, _update 14/14, _finish 13/13, _init 8/8;
     - scan_tokens 8/8; sort_in_place 4/4;
     - no byte store elsewhere.

     It costs nothing against the old code: the old lowering emits the same `MOVZX r, BYTE PTR [r]` after each store. A wide store's reload is never made, since the translation reloads only an output it reads (0 of 32). This is what [[bytes-level-passes]] would remove from both.
  9. **The clipped view at `Lend`** (copy_window): it costs nothing. The lend's routine is instruction for instruction the old one, so the old lowering already emits the clip.
  10. **The theorem's remaining forms** (item 3's list): the next round's brief.
  11. **The optimizer and the planner on the new layer.** The comparison translates the old planner's placement and lowers the optimizer's FunctionIR output. Stage 3 deletes the buffer nodes, so both must run on the bytes level, or on FunctionIR's word half before the translation.
  12. **Read-only views.** The old `Lend` puts back only a view marked `written`, so a callee's store into an unwritten view is lost; at the bytes level it lands. The translation is exact only where no callee stores through an unwritten view. Stage 3 needs that as a checked premise, or the view lent as an unwritten block.
  13. **Not needed by any row:** two-byte accesses and the typed copy ([[bytes-level-copy-and-halfwords]]); a past-the-end store (refused by both); `TableRead` (refused by both).
  14. **native_cat and native_tools compile through the program compiler** (`native_compile*`), not FunctionIR. Stage 3 does not move them, and nobody should assume it does (stage 7).
- 2026-11-26: **handoff, the access view** (item 5's first entry, ruled by the coordinator, not started here). What the change needs, as found:
  - **The language** (`bytes_level.hthr`):
    - `Instr::Store(bytes, place, value)` gains `view`, the width it stores from. `step` writes the low `bytes` bytes of the value's view at that width.
    - `Instr::Load(bytes, output, place)` gains the kind its output is held at. `step` is unchanged: it binds every width, as now.
    - `Instr::check` (line ~591) refuses a view narrower than `8 · bytes`, and whatever the lowering cannot emit, with a reason.
  - **The scope and kinds** (`bytes_level_scope.hthr`): `output_of` (~84), the step lemmas (~334, ~1340), and the check-binds lemma (~402).
  - **The lowering** (`bytes_level_lower.hthr`):
    - `emit_load_at` and its byte and word variants, which record `Held(output, Word)` at ~341, ~380, ~682–730 and ~853. They record the stated kind instead, so a `Narrow(32)` load is followed by `ByteSwap(32)` with no move.
    - `emit_store_at` and `emit_store_at_emits` (~998, ~1028) look the value up at the view's kind.
    - The `Loads`/`Stores` claims (~982) and `load_holds`/`store_holds` (~1250–1424).
  - **The routines' placement walk** (`bytes_level_routines.hthr` ~746–803); renaming (`bytes_level_renames` ~243); the canonical form (`bytes_level_canonical` ~88).
  - **The translation**:
    - `BufferStore` is a store from the 64-bit view; `WideStore(4)` from the 32-bit view.
    - `BufferLoad` is held as a word; `WideLoad(4)` held narrow.
    - The placement translation (`bytes_level_compare`) is unchanged: the places are the same.
  - **Probes**: every existing probe's answer kept at the 64-bit view.
    - The two smallest programs from item 4's cause 3 become probes with their theorems.
    - One refused control: a four-byte store from a view the value is not held at.
  - **Then** re-run `scripts/bytes-level-compare` and `--gates`.
  - **An open question**, unverified: whether `Typed`'s word kinds should carry a width instead. The per-access statement looks sufficient, since a load binds every width and a store's view is a lookup at a kind. But calls' and answers' kinds were not checked against it.
- 2026-11-26, the round's final verification:
  - `scripts/fmt --check` and `scripts/lib-closures` clean;
  - `scripts/linked --check` unchanged;
  - `HEATHER_PR_NATIVE=all scripts/test --pr`: `== suite: 4139 passed, 0 failed, 3 ignored ==`.

  The run was over item 3's theorem in the library. Later commits changed only the docs and this log.

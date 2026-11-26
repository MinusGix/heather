---
title: The bytes level's loads and stores name the view they use; the loop's back edge; the comparison again
status: open
labels: [native,function-ir,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-26
updated: 2026-11-26
---

The bytes level's word ids have a view at every width (FunctionIR's valuation inside `Compute`), and views at different widths are independent in general. The lowering holds an id at one kind. Before this round a `Store` and a `Load` silently meant the 64-bit view and the kind `Word`. So a `ByteSwap(32)` result could not be stored by a four-byte store, and a four-byte load could not feed a `ByteSwap(32)`. That refused the four SHA-256 buffer rows and `scan_tokens` ([[bytes-level-translation]], item 4, cause 3; `docs/language/ownership-design.md` §17.8).

The coordinator's ruling, built here:
- `Store(bytes, view, place, value)` writes the low `bytes` bytes of the value's view at width `view`. The lowering asks for the value at that view's kind (`Word` at 64, `Narrow(32)` at 32).
- `Load(bytes, view, output, place)` binds the output at every width, as before, and the lowering records the stated kind.
- Validity refuses a view narrower than the access, and any view but 64 and 32.

Beside it:
- The plain loop's back edge jumps straight to the head where the continuing arm moves nothing.
- The translation drops a dead reference `Move`.
- The comparison is re-run over every export row and the gates.

## Log

- 2026-11-26: **The check the coordinator asked for first.** Do narrow-held values cross a call, a loop's state or an answer? No, by construction, in both pipelines:
  - In FunctionIR, every boundary is a 64-bit word port: `Call` (`word_ports`), `Loop` inputs/next/outputs and the bound, `Lend`, `Function.parameters` and `result`.
  - The old lowering moves a port with `File::move_outputs` → `file.place(Held(id, Kind::of_width(64)))`, an exact kind lookup with no widening from `Narrow(32)`.
  - At the bytes level, `Typed` appears only at calls, loops and a routine's parameters and results, all taken at width 64.
  - A `Branch` joins by `File::meet`, per register, which keeps a narrow kind only where both arms agree.
  So `Typed` carries no width; the per-access statement suffices.

  **Item 1, the access view, landed** (ffbebd2).
  - The language (`bytes_level`):
    - `Store(bytes, view, place, value)` writes `low_bytes(bytes, view_word(words, view, value))`, where `view_word` is the 64-bit word at 64 and the `view`-bit view resized otherwise.
    - `Load(bytes, view, output, place)` keeps its meaning: it binds every width.
    - `Instr::check` asks `access_ok = width_ok ∧ view_ok`. `view_ok` is the 64-bit view at any width, or the 32-bit one at four bytes or fewer. So it refuses a store from a view narrower than its bytes, a load held narrower than what it read, and any other width.
  - The lowering (`bytes_level_lower`):
    - `view_kind(view)` is `Word` at 64 and `Narrow(view)` otherwise.
    - The store emitters look the value up at `view_kind(view)`; `view_word_held` turns its `Rep` into the view's word.
    - The load emitters record `Held(output, view_kind(view))`. `Loads` states the output's `Rep` at that kind, and `written_leaves` takes the kind.
    - `load_holds` goes through a new stage lemma `load_view_held`: at 32, the word read from four bytes or fewer is its 32-bit view widened (`word_of_bytes_round`, from `word_of_few`). `store_holds` uses `view_word_agrees`.
  - Restated with the view: the scope lemmas, the canonical form, renaming, the routines' walk (`Instr::emit_grows`) and the compare's `instr_shown`.
  - The translation: byte accesses at the 64-bit view, and a wide access of n bytes at its `8n`-bit view (`wide_view`), which is `Narrow(32)` at four bytes and `Word` at eight, as the old lowering's `StoreSize::kind` and `WideLeaf`.
  - The theorem's node level (`byte_store_runs` and the leaf lemmas) needed only the new constructor arity: `view_word(_, 64, _)` reduces to the word.
  - Probes:
    - `swap_store_*` and `load_swap_*` (lower_tests): the two smallest programs, each valid, lowered, and with its `emit_emits` theorem.
    - The control `swap_store_wide_refused`: the same store from the 64-bit view is refused by the lowering, since only `Narrow(32)` holds the swap's result. Validity accepts it.
    - The views validity refuses (bytes_level_tests): `store_past_view_invalid`, `load_past_view_invalid`, `store_other_view_invalid`.
    - A narrow-held load answering its word.
    - Every existing probe keeps its answer at the 64-bit view.
  - Not in the handoff's list: `written_leaves`, `word_of_four` (now `word_of_few`), the canonical and renaming step lemmas, the compare's instruction encoding, and `cut_store_unprovable`'s `Stores`.
  - Verification:
    - `scripts/fmt --check` and `scripts/lib-closures` are clean, and `scripts/linked --check` is unchanged.
    - `HEATHER_PR_NATIVE=all scripts/test --pr`: `== suite: 4139 passed, 0 failed, 3 ignored ==`.
    - The inherited head's baseline run reported 4138/1. Its one failure was the library gate, which read these modules while they were being edited; every other target passed.
- 2026-11-26: **Item 3, the dead reference `Move`, landed** (8bc961c).
  - `Scope::memory`'s reference-`Move` arm now emits nothing where the function never reads the copy (`mem_nat(output, reads) = False`). That is the drop the rebound pure node gets: exact in meaning, since nothing reads the output.
  - The placement walk skips it, because its form is `Plain([])`.
  - The theorem covers word nodes only (a word's `Move` is unchanged), so only `pure_form`'s spelled motive changed.
  - No reference move was added to the language.
  - Probes: `dead_copy_dropped` and `answered_copy_kept` (from_function_ir_tests).
  - The per-row counts are in the comparison's entry.
  - Verification: `scripts/fmt --check` and `scripts/lib-closures` are clean, and `scripts/linked --check` is unchanged.
  - `HEATHER_PR_NATIVE=all scripts/test --pr`: `== suite: 4139 passed, 0 failed, 3 ignored ==`.
- 2026-11-26: **Item 2, first attempt (01c4136), reverted (9b5a90a).** A straight tail (test; `Jcc H`; `J:`), with its proofs (`PlainTail`, a counted taken-Jcc claim).
  - Every module and the suite were green, yet the first comparison refused every loop routine at `Program::lower`'s `laid_out()`.
  - The assembler model (`item_lands`, `JccLands` in `x86_64_asm_runs`) lands a JCC only forward.
  - So the proofs held under a premise no such program meets, and no test lowered such a loop by evaluation.
  - The coordinator's rule from this, for this round and after: **an emitter form is not landed until a program using it lowers by evaluation.** That means `Program::lower` answers `Some` for it by `refl` in a probe, and the comparison runs it.

  **Item 2, landed (7a56255): the tail jumps forward out and once back.**
  - The coordinator ruled the old shape, forward only. Corrected here: the moves must come first, since an exit needs the outputs in place.
  - The tail is now: moves; the exit bit's test negated; `Jcc J` (taken where the bit is set); `JMP H`; `J:`.
    - A continuing pass falls through the `Jcc` and takes the one counted `JMP H` (`claims_jump_item`).
    - One layout serves empty and non-empty moves.
    - The test is `branch_test` on the file after the moves, which `Keeps` describes.
    - A program whose moves overwrite the exit bit's register is now refused, where the jumped layout lowered it.
  - std additions only, in `x86_64_asm_runs`: `ConditionCode::negate` with `negate_holds`, and `Test::negated` with `negated_taken`. A bit's `TEST` becomes `CMP r, 0` with `NE`, because `Test` has no TEST-with-JNE form; the rows' exit bits are folded comparisons.
  - Proofs:
    - `plain_moves_run` (the moves block, the file after them kept) feeds `plain_leaves` (out to J) and `plain_turns_claim` (round to H).
    - `plain_step`, `plain_passes`, `plain_pass_stops` and `plain_passes_stops` take the file after the moves and its `Keeps`.
    - `plain_close`, `plain_close_emits`, `plain_close_stops` and `plain_close_grows` move first, then test.
    - `plain_turns` (uncounted) and `loop_turns`' use are gone, as are the old `plain_jumped` and `plain_back`.
  - **The rule, checked over every form.** Lowering by evaluation through `Program::lower` (routines_tests), before this round:
    - byte load and store at 64: `lend_lowers` and `echo_lowers`;
    - `Offset`: `lend_lowers`;
    - call: `lend_lowers` and `both_lowers`;
    - recursive call and branch: `down_lowers`;
    - loop with non-empty moves: `countdown_lowers`;
    - `Sys` read and write: `echo_lowers` and `rtl_lowers`;
    - `Exit`: `exits_lowers` and `exits_nested_lowers`.

    Forms whose only evidence was `Body::emit` (no layout premise) or a theorem under `laid_out`:
    - four- and eight-byte loads and stores;
    - the 32-bit view;
    - `LoadRef` and `StoreRef`;
    - a loop with empty continuing moves.

    Added: `countdown_straight_lowers`, with its done clause, and `accesses_lowers` (every memory node at both views). `Copy` has no emitter.
  - Verification:
    - `scripts/fmt --check` and `scripts/lib-closures` are clean, and `scripts/linked --check` is unchanged.
    - `HEATHER_PR_NATIVE=all scripts/test --pr`: `== suite: 4139 passed, 0 failed, 3 ignored ==`.
- 2026-11-26: **Item 3, corrected.** The copy sort keeps (`Move(64, 5, 0)`, a span's reference) was not dropped. `Function::reads` gathered every loop pass's reads unmoved, and sort's pass names its own parameter 5.
  - A pass reads only its parameters and what it binds, in a valuation of its own; `translate_region` adds them, moved, as `pass_reads`.
  - So the scope's reads of a loop are its inputs and bound (`scope_reads`, c2d7b8c). The copy is now dropped.
  - Count: sort_in_place 1, export rows 0.
  - The handoff's "the old code has no instruction for it" was not quite right. The old code moves it in one `MOV r12, RDI`; the new code emits nothing for it.

  **Item 4, the comparison** (export rows, then `--gates`), on the tree with items 1, 2 and 3.
  - Same bytes: sha512_t1, _t2, _next; sha256_t1, _t2, _next; sha256_init (1236, refused before this round).
  - Differ by loops alone (every non-loop routine the same; each loop the same shape):

    | Row | Old → new bytes | Loops |
    |---|---|---|
    | sha256_compress | 8172 → 8240 | 10 |
    | sha256_update | 8949 → 9007 | 9 |
    | sha256_finish | 9575 → 9647 | 10 |
    | count_newlines | 291 → 297 | 1 |
    | raise_span, list_raise_letters | 317 → 323 | 1 |
    | copy_span | 217 → 227 (REX) | 1 |
    | copy_window | 313 → 323 (REX) | 1 |
    | scan_token | 11557 → 11563 | 1 |
    | scan_tokens | 14564 → 14576 | 2 |

  - Gates:
    - add_wide, signal, stats and nested_true are the same bytes.
    - lower_bound 278 → 288 (REX).
    - utf8_valid_up_to 1488 → 1494.
    - sort_in_place 725 → 738: routine 0 is +6; routine 2 is +7, which is +10 for the loop less the dropped copy's `MOV`.
    - rsum is refused by the translation (levels).
  - Per loop: +6 bytes, or +10 where the counter or the flag needs REX. With the jumped layout (items 1 and 3 only) it was +8 / +12.
  - Per continuing pass, the old code runs 6 loop-control instructions (`TEST; JE`, `CMP; JNE`, `ADD`, `JMP`) and the new 7 (`CMP; JNE`, `ADD`, `MOV flag, 1`, `CMP; JE`, `JMP`). That is the old count plus the translation's `MOV flag, 1`. Both take one jump per pass.
  - Checked on every loop of every row and gate by the tail's instruction shape (`ADD; MOV; CMP; JE; JMP`), against the old `ADD; JMP`.
  - `ownership-design.md` §17.8 and the translation issue's stage-3 list are updated with these numbers.

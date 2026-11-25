---
title: The bytes-level language: words and references, a heap with a shadow, one meaning, placelessness as a theorem
status: open
labels: [native,function-ir,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Stage 2 of `docs/language/ownership-design.md` §17.5, first part: the bytes-level language as the design wants it (§17.3), built beside FunctionIR's memory half. This issue is the language and its meaning; its lowering to x86 and the translation from old programs follow it in the same stage.

## Scope

- **First, a reading** (an hour, reported in the log before building): are `lib/native/function_ir/function_ir_lower_structured.hthr` and the frame proofs of `function_ir_lower_calls.hthr` generic in the body's invariant, so that the structured-control lowering and the frames can be cited by a new memory layer, or are they stated over `Buffers()` so that they must be redone? Name the theorems either way. §17.4 calls this the unknown of the whole stage.
- **Values and kinds**: `Word` and `Ref` (a block and a byte offset); every id has a kind; validity checks kinds as it checks widths.
- **The heap**: bytes per block with a shadow of entries (which eight-byte slots hold a reference and to what), canonical (zero under an entry). Grown from `lib/native/reference_cells/reference_cells.hthr`.
- **Nodes**: a wrapper over the existing word `Node` (valid only where the wrapped node touches no buffer), and through a reference a load and a store at each width, a load and a store of a reference, an offset, a typed range copy. No node names a buffer by number. Structured regions, calls and loops over these nodes, reusing the existing shapes where the reading says they can be.
- **One meaning**: `run(p, f, args, heap) → Option<Answer>` with `Answer { words, heap }` and `Calls()` as §17.2 states them; a callee kind for a system call is left as a constructor with no cases yet (the world's design is being done separately). `Refines(p, q)`: every answer of `p` is an answer of `q`.
- **Placelessness**: `run_renames`, a run commutes with a renaming of blocks, proved once for the language.
- **Site facts**: a load or a store is defined where it is in bounds, does not cut a reference, and is inside what may be written; state those as the node's definedness, so a later lowering takes them as facts.
- Probes: the experiment's program (store a reference, load it, read through it) in the real language; a window passed as a reference and a length to a callee that writes it; two windows of one block written by one callee; each with its control.

## Done when

The language, `run`, validity and `run_renames` pass the library gate with the probes, the reading's answer is in the log, and nothing in `lib/native/function_ir`'s existing modules has changed.

## What it assumes from elsewhere

- **[[x86-memory-contract]]** owns `Injected`, `Sub` and `Site::Meets`, which this language's lowering will cite.
- **[[ownership-reference-cells-spike]]** (closed) is the experiment this replaces.

## Log

- 2026-11-25: Round 1, the reading (§17.4's unknown), before building. **The structured lowering is words and control only. The call and loop proofs are about memory through one clause, `Stack::Trail`, which they use only for stability under the frame's own stores. So the new layer can cite the first unedited, and the second after one small generalisation (stated below for the coordinator). It cannot reuse the `StructuredRegion` type itself, since that type's leaves are FunctionIR nodes with buffer nodes and its meaning is relational. The new language states its own region type with the same shapes, and its lowering will reuse the emission functions and the word-only proofs.**

  **`function_ir_lower_structured`: words and control only.** `Emits`, `MayEmit`, `emits_seq`, `may_emit_seq`, `emit_nodes_emits`, `branch_emits`, `StructuredRegion::emit_emits`, `finish_lowers`, `StructuredRegion::lower_lowers` and `StructuredRegion::lower_correct` are stated over `Site::Runs`, whose pre- and postconditions are predicates over `Gprs` alone (`file.Represents(values, g) ∧ facts`). Memory and `Buffers()` appear nowhere in them. They are tied to FunctionIR's `StructuredRegion` (`Lend`, `Call` and `Loop` emit `None`) and to `StructuredRegionHolds`, but only weakly: `emits_seq`/`may_emit_seq` take the facts as parameters; `branch_emits` needs only that the facts select an arm by the condition bit (`when_nonzero`/`when_zero`); `emit_nodes_emits` is at `NodesHold(values, nodes)` over no buffers, which for a node that touches no buffer is its equation. A word-only leaf of the new language is lowered by `lower_nodes` and proved by `lower_nodes_keeps`/`lower_nodes_guards` (`function_ir_lower`) unedited. The join (`File::meet`, `meet_left`/`meet_right`) and the label shapes (`branch_label`, `else_label`, `join_label`, `site.runs_branch`) carry over as they are.

  **`function_ir_lower_calls`, in three groups** (a classification of its 269 theorems by what their statements mention):
  - *Words, registers and frame arithmetic only (about 170):* `call_restores`, `args_restored`, `answer_slot_rep`, `answered_slot_rep`, `saves_restored`, `saved_fit`, `frame_allocated`, `frame_freed`, `frame_down`/`frame_up`/`frame_still`, `moved_rsp_*`, `prologue_moves` (memory unchanged), `Stack::lowered_at`/`raised_at`/`passes_*`, `loop_entry_sound`, `loop_exit_sound`, `loop_counter_*`, `compare_selects`, `Gpr::tests_zero_at`, `emits_in_seq`, `emits_in_weaken`, `kept_block_emits`, `emit_kept_nodes_emits` (over `EmitsIn`, whose memory clause is the frame's `Stack::Wrote` only), every `*_grows`, `Function::roomy_*`, `level_room_*`. Citable as they are.
  - *Generic in the memory invariant already, through a parameter `keep: M → Type` (8):* `epilogue_moves`, `epilogue_moves_words`, `loop_rounds`, `loop_stops`, `loop_enters`, `loop_marks`, `loop_leaves`, `result_moves` (with `Stack::LoopHead`/`Stack::LoopPassed`, which take `keep`). Citable as they are, at the new invariant.
  - *The file in the statement (about 90).* Everything through `EmitsOver`, whose memory clause is fixed to `Stack::Trailed` = `Kept ∧ Stack::Trail(lending, d, entry, now: Buffers(), memory)` = `WroteIn(d, lending.spans(), …) ∧ Stack::InMemory(lending, now, memory)`. This covers `emits_over_seq/weaken/still/at/some`, `branch_emits_over`, `call_spills`, `call_stages`, `call_moves`, `call_raises`, `call_returns`, `call_finishes`, `call_emits`, `call_step`, `lend_step`, `Site::loop_passes`, `loop_body_runs`, `loop_emits`, `loop_close_emits`, `StructuredRegion::emit_calls_runs`, `function_enters`, `function_closes`, `function_runs`, `program_step` and the `lower_program_*_correct` theorems. It also covers the file's own lemmas (`Stack::in_memory_put`, `in_memory_span`, `trail_put`, `trail_span`, `in_memory_lent`, `store_emits`, `load_emits`), which are exactly what `Injected` and its operation lemmas replace.

  **Which of the third group mention the file only where a parameter would do.** I read the proofs. The call sequence (`call_spills` … `call_finishes`, `call_step`) uses the file only through `stack.trail_store` (the trail is stable under a word stored in the frame or below, from `Stack::stable_in_memory`) and the `WroteIn` lemmas (`wrote_in_trans`, `wrote_in_deeper`, `wrote_in_own`, `wrote_in_frame`). The rest of their content is registers, slots and the stack. `call_step` additionally takes the caller-to-callee relation as hypotheses (`enters`, `leaves`), already over an abstract `inner` lending. `Site::loop_passes` uses `Buffers()` only as the type of the threaded state (`Head`, `Done` and `pass` are parameters). `loop_body_runs`/`loop_emits` reach memory only through `LoopHead`/`LoopPassed`'s `keep`. `emits_over_seq` takes `First`, `Second : Buffers() → Type`. `function_enters`/`function_closes` use `InMemory` only to carry it across the prologue's and epilogue's frame stores. `branch_emits_over` needs only that the facts pick an arm.

  **The small generalisation, not made here (for the coordinator's decision).** In `function_ir_lower_calls`, replace the memory clause of `EmitsOver` with a parameter. Take a state type `S` in place of `Buffers()`, and `Mem : S → M → Type` in place of `Stack::Trail(lending, d, s0.memory, ·, ·)`, with one law asked of it: `(now: S) → stack.Stable(w, Mem(now))`, which `Stack::stable_in_memory` discharges today. Do the same in `Stack::ArgsReady`, `Stack::Called`, `Stack::Entered`, `Stack::Closed`, and make `Site::loop_passes` generic in the state type. The theorems listed in the previous paragraph then hold at any `(S, Mem)`. The old layer is the instance `S := Buffers()`, `Mem := Trail(lending, d, entry)`. The new layer is `S := its heap`, `Mem := WroteIn(spans) ∧ Injected(spans, heap)` under the one lending of `Site::Meets`. Without it, the new lowering restates the call sequence, the loop's passes and the function's frame over its own invariant. That is roughly the 2,500 lines of `function_ir_lower_calls` from "Conditionals" through "Functions", the register and frame halves of each copied. With it, it restates nothing of them.

  **What this means for the new language's regions.** Not wrap, not parameterise: `StructuredRegion` cannot be parameterised over its node type without changing `function_ir` (and every module over it), and wrapping it would carry `Lend`, `Sequence` and the relational `StructuredRegionHolds` into a layer that has none of them. The new language states its own region type with the same shapes (a leaf, a composition, a conditional on a one-bit word, a call, a bounded loop with FunctionIR's `Loop` fields). The shapes are kept exactly so that the lowering can reuse `emit`'s label scheme, `File::meet`, the loop's registers (`LoopRegisters`, `loop_entry`, `loop_exit`) and the call's code (`File::emit_call`), and cite the word-and-control theorems above.
- 2026-11-25: Round 1, the build (branch `claude/bytes-level-language`). **The language, its one meaning, validity by kinds, the site facts, a canonical heap and placelessness are built and proved. The probes pass, each beside its control. Nothing in `lib/native/function_ir`, `lib/std/arch/x86_64` or `lib/native/reference_cells` changed.**

  **Modules** (`lib/native/bytes_level/`):
  - `bytes_memory`: `Memory` (the experiment's `Heap` and `written`), `Pointer`, `Piece`, the two primitives `Memory::take` and `Memory::put`, and the operations as them (`load`, `load_ref`, `store`, `store_ref`, `copy`). Site facts both ways: `Memory::take_some`/`take_of`, `put_some`/`put_of`, `load_some`/`load_of`, `store_some`, `store_ref_some`, `copy_some`. Renaming: `MemoryRenamed`, `Memory::take_renames`, `put_renames`, and from them `load_renames`, `load_ref_renames`, `store_renames`, `store_ref_renames`, `copy_renames`. The relation-carrying lemmas `Related`, `related_then`, `related_map_then`, `related_same_then`, `related_eq_map`, `related_map_eq`. Canonical: `Memory::Canonical`, `Piece::Canonical`, `Memory::take_canonical`, `put_canonical`, `store_canonical`, `store_ref_canonical`, `copy_canonical`.
  - `bytes_level`: `ValueKind`, `Typed`, `Locals`, `Config`, `Instr` (`Compute`, `Load`, `Store`, `LoadRef`, `StoreRef`, `Offset`, `Copy`), `Body` (`Leaf`, `Seq`, `Branch`, `Call`, `Loop`), `Callee` (`Local`, `System` over the empty `Syscall`), `Routine`, `Program`, `Answer`, `Calls()`, `run`, `Refines` (`refines_refl`, `refines_trans`, `Memory::Same`), and validity (`Instr::check`, `Body::check`, `Routine::valid`, `Program::valid`).
  - `bytes_level_renames`: `LocalsRenamed`, `ConfigRenamed`, `AnswerRenamed`, `PlacelessFn`, `Placeless`; `Instr::step_renames`, `run_instrs_renames`, `loop_run_renames`, `Body::run_renames`, `Routine::call_renames`, `tie_placeless`, `deep_placeless`, `program_placeless`; **`run_renames`** (a run on a renamed heap, its arguments renamed alike, is the run renamed) and **`run_words_alike`** (the words answered, and whether it answers, are the same under any renaming).

  **Probes** (`lib/_tests/native/bytes_level/bytes_level_tests.hthr`), each with its control:
  - *The experiment's program*: `cells_read_nine`. Controls: `cells_byte_of_reference` (a byte a reference holds), `cells_read_only` (a store into a block the run may not write), `cells_word_argument` (an argument of the wrong kind). Beside them `cells_byte_beside`.
  - *A window as a reference and a length, written by a callee*: `lend_first`, `lend_between`, `lend_last`, `lend_to_end`. Control: `lend_past_end`.
  - *Two windows of one block written by one callee*: `both_first`, `both_second`. Control: `both_aliased`, the windows one place, which holds what was stored last.
  - *Validity*: `add_of_reference_invalid` beside `add_of_words_valid`; `call_kind_invalid` beside `call_kind_valid`; every probe program `valid`.
  - *A store that cuts a reference*: `cut_store_refused`, `cut_byte_refused`. Controls: `store_beside_kept`, `whole_store_replaces`. A typed copy: `copy_moves_reference`, control `copy_cut_refused`.
  - *Placelessness at one renaming* (blocks 0 and 1 swapped): `cells_words_alike` cites `run_words_alike`, and `cells_swapped_reads_nine` shows the instance answers. Control: `reference_answered`/`reference_answered_renamed`, a reference answered is renamed, not the same.

  **Reuse of FunctionIR.** The word half is FunctionIR's, unedited: `Node`, its evaluator (`Node::step`, `Node::defined`), `Node::pure` and `Valuation`. The regions are the language's own with `StructuredRegion`'s shapes (the reading explains why), minus `Lend` (a window is two parameters), `Sequence` (`Seq` of a `Leaf`) and the conditional's port lists (validity computes the join, what both arms bound alike). The loop's fields are FunctionIR's, with the state typed.

  **Choices** (each recorded in `docs/language/ownership-design.md` §17.6):
  - `written` lives with the heap. Stores are dynamic, so the meaning must refuse a store into a block the run may not write. Sent to the coordinator for the heap's move.
  - Every memory operation is a take or a put of a piece. So there are two site facts and two renaming lemmas, and the lowering needs one `Injected` lemma per primitive.
  - The heap is canonical by construction. That entries are apart is kept but not yet stated; [[bytes-level-passes]] needs it.
  - `Refines` compares heaps by `Memory::Same`; there is no function extensionality.
  - Validity checks kinds and not FunctionIR's widths.
  - `Offset` adds forward only.
  - The meaning is written with `Option::and_then`, so the renaming proof is one lemma per step kind rather than a transport per arm. This changed no answer: the probes passed before and after.

  **Cost** (`--timings`, fresh cache; the suite runs it at width one). Own declarations: `bytes_memory` about 0.5 s over 85 items, the costliest the canonical lemmas' `omega` (`placed_canonical`, `zero_in_window`, under 0.1 s each). `bytes_level` about 0.3 s over 64. `bytes_level_renames` about 0.27 s over 35, the costliest `Instr::step_renames_at` at under 0.1 s. The renaming proof grows linearly in the constructors. `run` on a probe is 1,500 to 7,000 kernel steps (under 11 ms), linear in the nodes executed. The module check is dominated by its imports (x86_64 by way of `reference_cells`), about a minute cold.

  **Filed for the rest of the stage:** [[bytes-level-lowering]] (under `Site::Meets`, with the coordinator's decision on the generalisation the reading states), [[bytes-level-translation]] (FunctionIR programs translated, and `crates/linked`'s exports compiled both ways), [[bytes-level-passes]] (each pass proved `Refines`, with the entries-apart invariant first).
- 2026-11-25: Round 2, the same day: **the coordinator's three changes, taken in place of round 1's meaning, not beside it.** There is still one meaning, one heap type and one notion of a call's answer.

  - **A family over fuel with four outcomes.** `run(p, blocks, n, f, args, heap, io) → Ran<Answer>`, where `Ran` is one of `Done(a)`, `Exited(status, io)`, `Going(io)` or `Stuck`; `Answer` is the words, the heap and the world. `Calls()` is a table at one fuel. A call spends one fuel, its body running at the rest, and a loop's pass spends one, so routines are tied by fuel: `levels` is gone and any routine may call any (routine `f` is `routines.nth(f)`). Monotone: `run_monotone`, `run_settled` and `below_then`, in `bytes_level_fuel`. Loops are plain: no bound, counter or `exhausted`. `Refines` has the three clauses, with `refines_refl`. Transitivity fails as stated, with a counterexample shape and a repair (`Stuck` carrying its history), in §17.6 of the note.
  - **The world in the state.** `Config` is the ids, memory and `Io`. `Sys(Read/Write)` restates `CallShape::cmd`/`answer` over a reference and a length. A read needs its window open (writable, inside its block, cutting and holding no reference). A failed read leaves the window undefined. A write sends the plain defined bytes at the window. Open, close and stat are a table to fill. `Exit(status)` answers `Exited`. Validity requires a descriptor and a count to be words, so a command carries no reference, and `run_renames` is the identity on `Io`.
  - **Undefined bytes.** `Memory` is now the heap and `undefined` (per byte, behind the accessor `undefined(b, i)`). `Blocks` (which blocks the run may write) is passed beside the program, so `written` is out of what a run answers. A piece carries its flags. A load is `Stuck` on an undefined byte (`Memory::read_bytes`, `read_bytes_some`). A put clears the flags over its window. Canonical now includes "an undefined byte is zero" (`placed_undefined_zero`, `flags_zero`, `Piece::undefined_canonical`).
  - **Reproved.** `run_renames` and `run_words_alike` (now on `shown`: the words, how the run ends, and the world), and `run_canonical`. The renaming proof lifts round 1's `Option` lemmas into `Ran` through `ran_then`, `ran_of_then`, `ran_of_map_then` and `ran_of_same_then`.
  - **Probes**, each with its control, rewritten for the new meaning and extended:
    - `undefined_load_stuck` with `stored_then_loaded`;
    - `echo_count`, `echo_first` and `echo_sent` (a read from a pipe and a write back), with `echo_past_read_stuck`;
    - `failed_read_undefines` with `answered_read_defines`;
    - `exits`;
    - `countdown_going` at too little fuel, `countdown_done`, and `countdown_settled` citing `run_settled`;
    - `write_reference_fd_invalid` with `write_word_fd_valid`;
    - `cells_no_fuel`.
  - **Evaluation shape, on the experiment's closure heap** (asked for by the coordinator). With k stores into one block and then a load, the cost is linear: 5.4k to 49k kernel steps for k = 8 to 128. With k stores into one block, each followed by a load of another, it is quadratic: 7.4k, 12.8k, 25k, 57k and 149k steps. So blocks as a list by number is the linear form; the contract's heap is changing to it.
  - **Cost now.** Own declarations: `bytes_memory` about 1.0 s (its largest item, `placed_undefined_zero`, is 0.47 s, mostly `omega`), `bytes_level` 0.44 s, `bytes_level_renames` 0.46 s, `bytes_level_fuel` 0.08 s and `bytes_level_canonical` 0.14 s. A probe's run is at most about 8k kernel steps.
  - **Not yet moved to the contract's heap.** That waits for the coordinator's reconciliation. My heap operations the contract lacks (`take`, `put` with pointers and flags, the typed `copy`, `read_bytes`, `open`) are stated over the heap's fields and `set_block`. They go beside the contract's operations when it lands.
- 2026-11-25: The two readings as tables, from which the rest of stage 2 is assigned.

  **1. The structured lowering and the frame and call proofs.** The full reading is the first entry of this log (round 1, the reading). In brief:

  | Group | Theorems | What their statements are over | For the new layer |
  |---|---|---|---|
  | Structured lowering (`function_ir_lower_structured`) | `Emits`, `emits_seq`, `may_emit_seq`, `emit_nodes_emits`, `branch_emits`, `StructuredRegion::emit_emits`, `finish_lowers`, `lower_lowers`, `lower_correct`; the join `File::meet`/`meet_left`/`meet_right` | registers only (`Site::Runs` over `Gprs`); tied to `StructuredRegion`/`StructuredRegionHolds` only in the facts | cite as is: word leaves through `lower_nodes`/`lower_nodes_keeps`/`lower_nodes_guards`; the arm-selection facts of `branch_emits` are restated for `Body::Branch` |
  | Registers, slots, frame arithmetic (`function_ir_lower_calls`, about 170) | `call_restores`, `args_restored`, `answer_slot_rep`, `answered_slot_rep`, `saves_restored`, `saved_fit`, `frame_allocated`/`freed`/`down`/`up`/`still`, `moved_rsp_*`, `prologue_moves`, `Stack::lowered_at`/`raised_at`/`passes_*`, `compare_selects`, `Gpr::tests_zero_at`, `emits_in_seq`/`weaken`, `kept_block_emits`, `emit_kept_nodes_emits`, every `*_grows`, `Function::roomy_*`, `level_room_*` | words and the frame's own `Wrote` | cite as is |
  | Generic in `keep: M → Type` | `epilogue_moves`, `epilogue_moves_words`, `result_moves`, `loop_rounds`, `loop_stops`, `loop_enters`, `loop_marks`, `loop_leaves` (and `Stack::LoopHead`/`LoopPassed`) | any memory invariant | cite at `keep := WroteIn ∧ Injected` (the loop ones per table 2) |
  | Through `EmitsOver` (the file in the statement) | `emits_over_seq`/`weaken`/`still`/`at`/`some`, `branch_emits_over`, `call_spills`, `call_stages`, `call_moves`, `call_raises`, `call_returns`, `call_finishes`, `call_emits`, `call_step`, `lend_step`, `Site::loop_passes`, `loop_body_runs`, `loop_emits`, `loop_close_emits`, `emit_calls_runs`, `function_enters`, `function_closes`, `function_runs`, `program_step`, `lower_program_*_correct` | `Stack::Trail(lending, d, entry, now: Buffers())`, used only for stability under the frame's own stores (`stack.trail_store`, `Stack::stable_in_memory`) and the `WroteIn` lemmas | generic after one change: the memory clause of `EmitsOver`, `ArgsReady`, `Called`, `Entered`, `Closed` a parameter `Mem: S → M → Type` with `(now) → stack.Stable(w, Mem(now))`, and `Site::loop_passes` over a state type `S`; otherwise restated |
  | The file's own lemmas | `Stack::in_memory_put`/`span`/`lent`/`wrote`/`same`, `trail_put`/`span`/`store`, `store_emits`, `load_emits`, `wide_*_emits` | `Buffers()` by number | replaced, not cited: one `Injected` lemma for `take` and one for `put` |

  **2. Loops when the bound goes** (`function_ir_lower_calls` unless named):

  | Theorem | Fate | Why |
  |---|---|---|
  | `loop_body_runs` | survives as is | one pass, from the head's state to the passed file; no counter in it |
  | `loop_leaves` | survives as is | exit bit set: the state moved out, the jump to the join |
  | `loop_exit_sound`, `loop_exit_out_sound`, `loop_exit_back_sound` | survive as is | the exit test's lowering is the exit bit's, not the count's |
  | `Stack::LoopHead`, `Stack::LoopPassed` (the head and passed invariants) | survive with the counter cut out | `LoopHead` states `read_gpr(counter) = remaining`; without it, the state registers and `keep` |
  | `loop_entry_sound`, `loop_entry_at_sound`, `loop_entry_with_sound` | survive with the counter cut out | they move the state into its registers and set the counter to the bound; only the state's moves remain |
  | `loop_rounds` | survives with the counter cut out | exit clear: the state moved round, then `AddRI8 counter, -1` and `JMP H`; the step goes |
  | `loop_close_emits`, `loop_emits` | survive with the counter and `exhausted` cut out | they compose the pieces above; the `exhausted` output and its flag go |
  | `Site::loop_passes` | survives, its induction changed | an induction on the passes left becomes one on the run's fuel: a run that answers took finitely many passes |
  | `loop_counter_zero`, `loop_counter_nonzero`, `loop_counter_step` | go | the counter's own arithmetic |
  | `loop_stops` | goes | "no passes left, the head jumps to X": no bound, no X |
  | `loop_enters` | goes | "passes left, fall through": the head falls through always |
  | `loop_marks` | goes | X sets the `exhausted` flag |
  | `LoopRegisters.counter`, `.flag`, `LoopRegisters::apart_sound` (its counter part) | go (the counter and flag); the state registers survive | |
  | `function_ir.hthr`'s `loop_runs_unexhausted`, `loop_runs_weaken`, `LoopRuns`, `LoopHolds` | go from the language; the measure argument becomes a separate termination fact | the bounded relational meaning; termination is no longer part of the meaning |
  | `function_ir_loop.hthr` (`loop_run`, `LoopFolds`, `step_fold_*`, `fold_body_*`) | does not carry over | a budgeted read-only loop interface that the lowering does not use |
  | optimizer rules (`function_ir_rule*`, `_optimize`, `_pass`) | unaffected | none states `LoopRuns` or the bound |
- 2026-11-25: Verified: `scripts/test --pr` on round 2 (the tree unchanged during the run): `== suite: 3517 passed, 0 failed, 2 ignored ==`. The library gate checks the five modules and the probes. No module of `lib/native/function_ir`, `lib/std/arch/x86_64` or `lib/native/reference_cells` changed.

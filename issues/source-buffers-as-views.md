---
title: One notion of buffer in Source: static, borrowed, arena and frame storage as views
status: open
labels: [native,design,memory,function-ir]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-10
updated: 2026-11-12
---

A `Source` buffer is a numbered static slot in the ELF's data region
(`Source.buffers`, `Layout`). Three rounds have each needed something else
and each would build it separately:

- the arena: a line is a span of the arena buffer, so `Bytes` must lower as
  a view (buffer, offset, length) and not only as a whole buffer
  ([[runtime-fn-arena-lists]], log of 2026-11-02);
- an export: the source span and the hash state are memory the caller owns,
  at an address that arrives in a register ([[native-library-exports-design]]);
- a procedure: local scratch is a block of its frame.

## Scope

- A buffer as an address held in a word plus a capacity. Static, borrowed,
  arena and frame buffers are instances that differ only in where the
  address comes from and who may write.
- `Target::Placed`/`Held` and the byte nodes' lowering (`BufferLoad`,
  `BufferStore`) over an address word; `Layout`'s static buffers as the
  instance with a literal address.
- Footprints as span sets (`lib/std/data/set/span_set.hthr`): two views are
  apart when their spans are, decided by the endpoints.
- `rt`'s `Bytes` held as a view, so a slice costs no copy.

## Done when

One program reads a static buffer, a borrowed span and an arena line
through the same nodes and the same lowering case, with a negative control:
a store through a read-only view is refused by the judgment.

## What it assumes from elsewhere

- **[[native-library-exports-design]]** decides whether this is the notion
  to build. Assumed here: only that it is asked the question first.
- **[[function-ir-buffer-state-edges]]** owns byte nodes in S4 with
  registers held across them.
- **[[state-location-and-frame-kit]]** owns point updates of a store.

## Log

- 2026-11-11: What U5's step 5d (byte nodes on the shared lowering, [[native-one-compiler]]) would take today, read off the code after step 5c, and why it reads as part of this issue:

    - The shared leaf (`emit_leaf`, `function_ir_lower_calls.hthr`) takes a buffer's home as two values of its scope, address and length (`Lent`), and lowers a load or a store only where the path knows the index below the length (`File::bounded`). A program's byte node tests the index itself and reads the address off the layout (`Prog::byte_to`, `byte_from`). So the program side would keep its test and hand the access to the leaf with the home loaded as two immediates, which is this issue's "static buffers as the instance with a literal address".
    - The leaf's theorems are stated in the function compiler's frame: what a leaf leaves is `Stack::Trailed(lending, d, …)`, stores below offset `d + 64`, the 64 bytes at RSP being a function's spill slots. A statement's frame words sit exactly there since step 5b. No leaf stores to the stack, so the leaf theorems (`kept_block_emits` through `emit_leaf_runs`) hold at any bound; they would be restated over a bound `i`, with the `d` forms their instances at `d + 64`. The alternative, 64 bytes of slack in `Target.roomy`, moves the top theorem's `deep` for nothing a program uses.
    - The program side then proves a byte node from the lending it already gives its callees (`Target::lending`, `loan`, `in_memory`, `based_left`), with a register file and a valuation built by hand at the leaf, R10 named in the file since a leaf keeps only the callee-saved registers. That is longer than `goes_byte_to` and `goes_byte_from` are now: the machine fact shared is one MOVZX and one byte MOV.
    - So the step pays when the home is a value and not a layout constant, which is this issue. Built before it, the bridge is written for immediates and rewritten for words.
- 2026-11-11: Minus chose (2026-11-11, on the decision card) to do U5's byte-lowering step here, with buffer views, and the export first. The scoping in the entry above is what the step takes; `docs/native-procedures-are-functions-design.md` §3 records the move.
- 2026-11-12: Views, steps V1 to V4a (docs/native-library-exports-design.md §3.1), on PR #551:

  - V1 `lib/std/data/list_window.hthr`: `List::window` and `List::put_window` with the lens laws; putting back what was read holds of any window.
  - V2 `lib/std/arch/x86_64/x86_64_views.hthr`: a `Loan` over parts of spans from the lender's (`Loan::view`), a trail in the views as a trail in the spans, and what the spans read after.
  - V3: a conditional's false arm records `Known::Falsity`, and `File::at_most` reads `a <= b` from it.
  - V4a: `Lend(views, callee, arguments, result)` in the IR, a call over views, with its meaning in every layer and an arm in every recursion over regions. The lowering refuses it by name; a statement does not lend (`StructuredRegion::scoped`).

  What changed from the first design: a leaf, not a region with a body. The callee's contract and the region theorem are at one lending for the program, so a body over another file would have been the induction hypothesis at another lending for everything in it. Next are the contract at every lending (V4b) and the lowering (V4c). The coarse store rule the views expose is [[function-ir-store-marks-per-function]].
- 2026-11-12: V4b built: the lowering's contract at every lending, and a function at a time. A lend's callee runs under the views' lending and not its caller's, so the contract a region is lowered against (`Site::CallsLent`, `function_ir_lower_calls.hthr`) is now at every lending of the program's counts, each function under one that lets it write what it needs (`ProgramNeeds`, `function_ir_writes.hthr`; as rows of marks, `program_marked`). The program's induction gives it (`emit_functions_calls_lent`, `lower_program_lent_needs`) and the statements at one lending are its corollaries for a program with no call over views. A function at a time was not in the plan for this step: one list of marks for a program cannot lower two views of one buffer (`issues/function-ir-store-marks-per-function.md` has the account, and is built here but for the certificate's text). §3.1 of the design has a paragraph on it.

  Next is V4c, the lowering of the call itself. What it needs that is not there yet: the views' lending has the views' spans only pointwise (`Views::spans` against `Lending::spans`), so `Loan` and `WroteIn` want a transport across pointwise-equal spans; the call theorems (`call_returns`, `call_emits`, `emit_call_runs`) take the CALL step as a premise, so a lend supplies its own step at the views' lending; and the lowering's checks (`File::at_most` for each view's bounds, the home of the scope, a written view's buffer no other view's).
- 2026-11-12: Views, step V4c (docs/native-library-exports-design.md §3.1), on PR #551: the function compiler lowers a call over views and proves it.

    - The code is two leaves the lowering had: the views' nodes (`emit_leaf`), then the call on the views' homes (`File::emit_call`), under checks of the views (`views_lent`, `lib/native/function_ir/function_ir_lower_views.hthr`): a view lies in a buffer the scope has a home for, with its bounds known of the path, the constant 0 or the buffer's length; a view to write is the only view of its buffer.
    - The proof is the call's with the CALL's step general (`call_step` for a callee entered under any lending; `File::emit_call_steps`), a lend being the instance at the views' lending (`Lending::lend`, `lend_step`), from `Lendable` and the machine laws of V2 with two transports added (`Loan::onto`, `Stack::wrote_in_onto`).
    - A program with a lend is stated a function at a time: `compiled_returns_needs`, and by evaluation with rows `compiled_returns_marked` (`function_ir_compile.hthr`).
    - A loaded constant is now known to the file as a folded one is (`File::constant`), which is what lets a view from a buffer's start through without a comparison.
    - Probes: `lib/_tests/native/function_ir/function_ir_lower_views_tests.hthr` (a window lent to write, a whole buffer under another number, two views of two buffers, each stated against its run; six refusals with the report each gets).
    - Left: two views of one buffer ([[views-of-one-buffer-apart]]); register room in a function with several homes ([[function-homes-live-to-function-end]]); V4d, V5, V6.
- 2026-11-12: Views, step V4d (docs/native-library-exports-design.md §3.1), on PR #551: a program links functions that call over views.

    - The placeless check has the lend's case (`function_ir_placeless.hthr`): a view's base is hidden from the lend on (`views_taints`), no view starts or ends at a hidden id (`views_clear`), and the homes and arguments reach the callee as a call's do. Both theorems have the arm (`StructuredRegion::eval_apart`, `run_apart`), so `program_run_placeless` holds of a program that lends. `program_placeless_lendless` is gone with what it said.
    - Rows of marks are found by a search and checked (`function_ir_rows.hthr`, `program_rows`, `program_rowed`): each function's own stores, then its callees' rows, a pass for each function. Nothing is proved of the search; `Prog::links` checks its answer (`program_linkable`) and the contract is from the check (`emit_functions_after_lent_calls_needs`, `Prog::links_calls`).
    - The control of this issue, at the functions' door: a callee that stores through a view lent to read has no rows that hold (`lends_read_stored_no_rows`, `lib/_tests/native/function_ir/function_ir_rows_tests.hthr`), so the program does not link (`view_source_read_refused`, reason 17).
    - A whole program: `view_program` (`lib/_tests/native/native_compile_tests.hthr`), whose statement calls a function that lends its second buffer whole as its callee's first. `write-elf` writes it with its certificate checked, and it exits with the byte stored through the view (`crates/cli/tests/native_cat.rs`). The Rust readers of a spelled source learned the lend's spelling (`lowered.rs`, `allocator.rs`).
    - Left: a statement that lends, the arena's line and `rt`'s `Bytes` as views, and the done-when program reading a static buffer, a borrowed span and an arena line through the same nodes (V5); step 5d (V6).

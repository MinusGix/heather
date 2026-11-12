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
- 2026-11-12: What the languages above take to lend a view (V5), read off `rt` after V4d and not built:

    - On the surface a view is the library's window: `callee(span.window(a, b), length, …)`, and for a span written the callee's span put back (`span.put_window(a, part)`). No syntax is new.
    - A function that writes is a function of one span (`FTm::Source`, `runtime_file.hthr`), and a loop is lent one span ([[runtime-loop-over-several-spans]]). `compress(state, block)` with the state written and the block read is two spans before it is a view, so that issue comes first.
    - In `rt` the place for a call over windows is the file layer (`FTm`), whose meaning threads the written span. Its callees are meanings over one fixed list of read spans (`FWorld.writers` beside `FWorld.rest`); a callee read over a window of a read span needs them at every such list, as the pure functions' are (`FWorld.callees`).
    - A pure term (`Tm`) is stated against the evaluation over one fixed file (`Answers`, `Tm::CallsAgree`), which cannot say a view. A pure call over a window goes through the file layer, or the fixed-file evaluation takes callees that read (`Readers`), which touches every theorem over `eval_over`.
    - Step 5d (V6) as scoped on 2026-11-11 pays when a statement holds a home as a word, which is a statement that lends (V5c). Before it the bridge is written for the layout's literal addresses and is longer than `goes_byte_to` and `goes_byte_from`.
- 2026-11-12: V5a, first part: a loop that reads is lent any number of spans ([[runtime-loop-over-several-spans]], closed). The generator's family is keyed by the list of a file's first spans (`Setup::GuardedSpans` at any `lent`), and `differ_sum`, a loop over two spans, has its `agrees_over` at every file and compiles with its certificate. So of the two things the scoping above put first, the loop's is done; the writer's is next: a function that writes is a function of one span (`FTm::Source`), and `compress(state, block)` writes one span and reads another. What the loop met is registers (four home words kept in place for two spans), logged on [[function-ir-values-in-kept-registers]].
- 2026-11-12: V5a, second part: a `runtime fn` that writes its first span reads the spans after it.

  The file layer's meaning already read the whole file (a computation's pure terms are read at `Cons(own, rest)`), so nothing below the class moved. What was of one span:

  - the source's type: `FTm::Source(tys, lent, ps, r)` now takes each read span's bytes before its length word, and `FTm::source_at` reads them from `rest` (`FTm::read_at`);
  - the class's table of writers, fixed over one `rest`: `CompileSpan.writers` is now the writers' meanings at every `rest` (`FTm::sems_cons`), which is what lets a caller's theorem be read at each file;
  - the reflector's gate (`rt_file_codes` answers the count of spans; a span only read is a parameter span `j ≥ 1` in `rt_span`; a call passes the read spans on, `rt_lent_args`);
  - the generator (`runtime_span_publish` at any count; `f::runs_over` states the function at `Setup::span_at(rest, k)`);
  - `compile-x86`'s gate (`Shape::runtime_written`): a writer of its first span whose later spans are unmarked. `copy_byte` exports as `(span mut, span, word) -> word`.

  Probes: `lib/_tests/native/runtime/runtime_span_reads_tests.hthr` (`copy_byte`: runs, short read, short write, stated at every file, marks `[True, False]`, placeless, lowers; `copy_pair` calls it twice).

  Owed, third part: a loop that writes and reads another span. `FFun::Guarded` is at one fixed `rest` and the loop's `ext` companion asks its recursions to agree at every read span, so the generator refuses it by name. Needed is the family keyed by the rest of the file (`FFun::GuardedBy` and a theorem to `FFun::Guarded` at each rest), as `Fun::GuardedBy`/`Fun::guarded_by` are for a loop that only reads. A copy of one span into another is the probe and the first linked export with a `span mut` and a `span`.
- 2026-11-12: V5a, third part: a loop that writes one span reads others.

  - `FTm::tail_sem_ext`, `FFun::GuardedBy` and `FFun::guarded_by` (`rt_file_loop.hthr`): the writer's family with its recursion keyed apart from its worlds, and `FFun::Guarded` at each world from it, the analogue of `Fun::GuardedBy`/`Fun::guarded_by`. The measure is keyed too, so it may read the spans read.
  - `FFun::GuardedSpans`, `FFun::guarded_spans`, `FFun::measure_at` (`runtime_file.hthr`): the worlds are the rests of the file, the key a rest's first `lent - 1` spans. `FFun::compile_measured` takes its measure and its bound at each rest.
  - `runtime_span_measured` (`runtime.hthr`) is one path at any count of spans; a loop over one span goes through it with no span read, and `raise_span`'s compiled bytes are unchanged (`scripts/linked`).
  - Probes: `xor_from` and its caller `xor_all` (`runtime_span_reads_tests.hthr`), stated at every file.
  - Export: `copy_span(out: span mut, text: span, count, from)` in `native_tool_spans.hthr` and `heather_linked::spans`, six words in the six argument registers. Rust tests against a reference at every pairing of lengths, inside larger buffers, between unmapped pages on both spans, on empty slices and at both stack alignments.

  V5a is done as far as spans go: what is left of it is the lend itself (a `runtime fn` calling over a window, through `Lend`).
- 2026-11-12: V5a, the lend, first stage: the callees' meanings and the link at every rest of a file.

  A callee called over windows runs on a file of the windows, which is another rest than its caller's. Three statements were at one rest and are now at every one, with no change to what a call on the caller's own file uses:

  - `FWorld.writers` is the computations' meanings at each rest (`FTm::called` reads them at the world's own);
  - `FTm::CallsAgree`'s third part answers each computation at every rest;
  - the link's family is every span with every rest (`SpanFile`, `span_file`, `span_sources`), so `Compile::spanned` and `CompileSpan::spanned` take no rest and their two lists are checked at every rest and span (`span_every`), still by conversion. `f::runs_over` is the family's statement at `span_pair(span, rest)`.

  Next: the term (`FTm::Lend`, a computation called over windows of this function's spans), its meaning with the written window put back, its lowering to the IR's `Lend` and the once-proof against `StructuredRegion::run`'s clause; then the reflector for `callee(span.window(a, b), …)` and the generator.
- 2026-11-12: V5a, the lend, second stage: the term, its meaning, its lowering and the once-proof, in the file layer.

  - `FTm::Lend(f, views, args, body)` with `FView(span, home, start, end)` (`rt_file.hthr`): the span's number in the file (0 the written one), the variable holding its place, and two word variables for the window; the start is absent for a window from the first byte. The first view is the written span and the later ones are read (`FTm::own_first`). The meaning (`FTm::lent`) is the callee's meaning at the file of the read windows (`FTm::lent_file`), applied to the written window, a place and a length per view (`FTm::lent_words`) and the arguments, with the written window put back by `put_window` at its start.
  - The lowering (`FTm::lower_lend`, `rt_file_lower.hthr`): a `Const 0` for each view from the first byte, two home ids per view, one `Lend` region, the result moved to a fresh port. Its once-proof is `FTm::lend_sound`, a `StepHolds`, so `FTm::lower_sound` and the loop's `FTm::tail_sound` (`rt_file_loop.hthr`) gained one arm each. The reflector's equality and printer and the generator's quoting know the term (`rt_file_reflect.hthr`, `runtime.hthr`); neither reads a lend from source yet.
  - The window's ends are variables because the function compiler's facts are keyed by port: a view is taken where arms on the way say `end <u start` and `length <u end` are false of those ports, or where the start is the constant 0 and the end the buffer's own length. So the source this reflects is `callee(span.window(a.toNat(), b.toNat()), b.sub(a), …)` with `span.put_window(a.toNat(), r.after)`, and `callee(span.window(0, n.toNat()), n, …)` put back at 0 for a span under its length word. This shape is my reading, not a ruling.
  - Probes, with the terms written by hand (`lib/_tests/native/runtime/rt_file_lend_tests.hthr`): `carry_at` (a window of each of two spans) and `carry_from` (the whole written span, a window of the read one). Each is pinned by conversion at any spans, compiled by `FFun::lower_sound` over any file, run on bytes, and accepted by the function compiler under rows it finds (`[[True], [True]]`); controls for a window past either span, a backwards window, and a `¬` for the claim that the lend changes nothing; five refusals of the lowering.
  - The function compiler refused the first lowered lender for registers, with a function's homes planned live to its end. Fixed in the planner ([[function-homes-live-to-function-end]]).
  - A loop that lends (`each_body`, the same file) lowers and runs, and the function compiler refuses it: twelve values wanted at the call, nine registers. Pinned as `each_refused` with its report; logged on [[function-ir-values-in-kept-registers]]. The hash's loop over its blocks is this shape, so it waits on that issue.

  Next: the reflector reads the two source shapes above and the generator publishes them (third stage), then an export that lends.
- 2026-11-12: V5a, the lend, third stage: read from source, generated and exported.

  - The reflector (`rt_file_lend`, `rt_file_reflect.hthr`) reads a `put_window` link of the span's chain as a call over windows: `span.put_window(a.toNat(), r.after)` with `r = callee(span.window(a.toNat(), b.toNat()), b.sub(a), text.window(…), …, words…)`, and `span.window(0, n.toNat()), n` put back at 0 for a window from the first byte. A bound is the word whose `toNat` it is; the word after a window is held to the bounds and binds nothing. It reads the two hand-written probes' sources as exactly the terms written for them, and six refusals each say why (`rt_file_lend_tests.hthr`).
  - The generator needed no change: four `runtime fn`s that lend publish their programs and `f::runs_over` at every file (`lib/_tests/native/runtime/runtime_span_lend_tests.hthr`): a window of each span, a store confined to its window, the written span whole, and two windows lent to a loop (`xor_window` over `xor_from`).
  - `compile-x86` exports one. A program that lends is stated by a row of marks per function (`compiled_returns_marked`), so the exporter reads `program_rows` back (padded to each function's buffers) and writes it as a literal the certificate checks by `program_marked` (`Shape::runtime_written`, `crates/cli/src/native/verified.rs`). `runtime_file.hthr` imports `function_ir_rows` so that the search is in a writer's scope.
  - The export: `copy_window(out: span mut, text: span, from, end)` in `native_tool_spans.hthr`, `heather_linked::spans::copy_window`: three comparisons, then `copy_span`'s loop lent the window of both spans. 553 certified bytes. Rust tests against a reference at every pairing of lengths with the window's ends on both sides of both and of each other, inside larger buffers, between unmapped pages, on empty slices and at both stack alignments.

  Found on the way: the kernel runs out of fuel on the probe sentence that a lender and a loop lower together ([[kernel-fuel-lowering-a-lender-and-a-loop]]); the export's certificate is by pieces and does not meet it.

  V5a is done but for a loop that lends ([[function-ir-values-in-kept-registers]]). Left of V5: V5b, V5c.

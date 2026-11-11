---
title: One native compiler: join write-elf and compile-x86 before exporting
status: open
labels: [native,design,compiler,memory]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-11
updated: 2026-11-11
---

Minus (2026-11-11): "Unify first and then export." `write-elf` and
`compile-x86` share FunctionIR and the verified lowering of a region and
have grown apart above it. Design and order:
`docs/native-one-compiler-design.md`.

## The three joints

1. A program cannot call a compiled function: `Source` has functions in
   its meaning and `StructuredRegion::code` refuses every `Call` region.
2. Buffers exist on the program side only, compiled by its own byte-node
   code; the function compiler refuses byte nodes.
3. Two kinds of call: System V functions, and `Source` procedures with
   their own convention and global word homes.

## Rounds

- **U1.** `Stack::Wrote` (the stores a call may make) replaces `Unchanged`
  in the function compiler's post; today's `compiled_returns` is its
  corollary. Absorbs [[x86-call-memory-footprints]].
- **U2.** `Source`'s `Call` region compiles to a CALL of a function
  compiled into the same program.
- **U3.** Buffers read through one home ([[function-ir-buffer-state-edges]],
  [[source-buffers-as-views]], [[runtime-default-setup-soundness]]).
- **U4.** Buffers written; `write-elf`'s byte nodes move to the shared
  lowering.
- **U5.** Procedures are functions whose bodies have effects, words in
  frames, a tree-valued claim ([[native-procedure-contracts]]). Its own
  design note first.
- **E.** Export ([[native-library-exports-design]], [[self-lexer-linked]]).
  Needs only U1 and U3; last because that is the order asked for.

## Done when

A `write-elf` program and a linked export are built by the same function
compiler: a program's helper is a `runtime fn` called by CALL, a buffer is
lent to a function by a program and by Rust through the same lowering
case and the same premise, and `Source` has one kind of call.

## Log

- 2026-11-11: U1 built: `Stack::Own`/`Stack::Wrote` in x86_64_stack.hthr; `CalleePost` and `Framed` state the stores; `wrote_unchanged`, `wrote_resident` and `compiled_returns_keeps` are the corollaries; no emitted byte changed. Next is U2.
- 2026-11-11: U2 built: a `Source`'s `Call` region compiles to a CALL of a function the function compiler emits after the program's own code (`Prog::function_call`, `Prog::links`, native_compile.hthr; R10 carried in RBX across the call, so no allocator changes). The call is proved from the function's contract (`Target::functions_run`, native_compile_function.hthr: `Site::moves_call` on `Returns`, `Target::Held` kept by `Wrote`), and `native_compile_correct` covers a source with functions, with or without procedures; its stack premise gains a term per function. `write-elf` spells the functions in the literal (`Source::spelled` tag 3), carries the placement of their values in the homes (`Homes.places`, from `plan_program`) and states the linking as one equation. Runs: tr through a called function beside GNU's, a tool calling a `runtime fn` that calls another, a procedure and a function in one file (crates/cli/tests/native_tools.rs). Refusal reasons 16 and 17 name a call that does not fit and functions that do not link. Limit kept: the functions' linking is one statement in the certificate, so a called function is as large as one declaration lowers ([[native-function-emission-in-parts]]). Next is U3.
- 2026-11-11: U3a built: the function compiler reads a buffer it is lent (design note §2.3). Meaning and evaluator over a program's numbered buffers (`StructuredRegionHoldsOver`, `Function::Computes(…, buffers := …)`, `program_callees_over`, `program_eval_over`, `program_eval_reads`); a function says how many it takes (`Function.lent`), buffer `k` its parameters `2k` and `2k + 1`. New `function_ir_lower_reads.hthr`: a home is two values of the scope (`Lent`), carried through a loop as state its passes hand on (`loop_carried`, a search held to `carried_sound`) and renamed after it (`StructuredRegion::lends`); the bound is a comparison the path knows (`Known::Truth` in the arm a conditional selects, `File::bounded`); the load is base, plus index, byte load. The contract lends (`Lending`, `Stack::CalleeLent`, `Site::CallsLent`), the old contract its instance at `Lending::none()`, so nothing that lends nothing moved. Theorems `lower_program_lent_correct` and `compiled_returns_lent`; probes and eight refusals in `lib/_tests/native/function_ir/function_ir_lower_reads_tests.hthr`. U3 is split: U3b a program's call passes buffers, U3c `rt` lowers `Get` and `Len`. U3b needs two things the note now states: a region's call answered over its buffers as they are, and placeless functions (a base read only as a home), so a program's tree need not mention where a buffer lies.
- 2026-11-11: Language finding from U3a, filed: [[defaulted-parameter-recursion-and-overapplication]] (a defaulted parameter cannot be handed to a recursive call and blocks applying a function's result in the same argument list; why the evaluator has `_over` forms beside the defaulted ones).
- 2026-11-11: U3b's first piece is built: `lib/native/function_ir/function_ir_placeless.hthr`. `StructuredRegion::placeless` checks that an address id is read by no node, tested by no branch, passed only at a callee's address place, and carried by a loop only where it came in hidden; `program_eval_placeless` proves a placeless program's functions answer alike at every address word, over any buffers. Probes in `lib/_tests/native/function_ir/function_ir_placeless_tests.hthr`. Left for U3b: answering a program's `Call` over its buffers (`StructuredRegion::run`, `Source::denote`), the call's code supplying static homes, `Lends` from the data region, and the tool. Also fixed here: the Rust tests' hand-written module lists (`function_ir_compile.rs`, `function_ir_lower_calls.rs`, `function_ir_lower_loops.rs`, `linux_wp.rs`) had not followed the reads module and the regenerated read-loop closure; sixteen tests failed on "unknown module" and on a module listed twice, none on a proof.
- 2026-11-11: U3b built. (1) Meaning: a region's calls are answered by `Readers()` (buffers, then callee and words; `function_ir_state.hthr`), a source's by `program_readers` (`function_ir_placeless.hthr`): a function lent `k` buffers is evaluated over the program's first `k` (`lent_buffers`) at address zero; for a function lent none this is `program_eval` by evaluation, so earlier certificates state what they did. (2) Code: `Prog::function_call` passes each lent buffer's address and capacity as immediates in the first registers (`Layout::homes_block`, in the block that carries R10) and the words after them; `Layout::function_fits` checks the arity after the homes, six registers and that the file has the buffers; `Prog::links` checks `program_placeless` and emits under `program_counts`. Code for a function lent nothing is unchanged. (3) Proof: `Target::Answered`/`answers_of` cite `Site::CallsLent` at the placed homes and turn the answer into the stated one by `program_eval_placeless` (`function_ir_lend.hthr`: `homes_apart`, `args_lent_placed`, `program_counts_lent`); `Target::buffer_readable` and `Target::lent_all` give `Stack::LentAll` from the claim between statements and `held_wrote`. `native_compile_correct` is unchanged in statement. (4) write-elf spells each function's `lent` (`List::spell_functions`, `lowered.rs`; the allocator mirror skips it); refusals 16 and 17 say what they check. (5) Runs: `wc_l_called_tool` (`native_tools.hthr`), wc -l with each read's newlines counted by `count_newlines` (`native_tool_spans.hthr`, FunctionIR by hand until U3c), held to GNU wc in `native_tools.rs`; probes in `native_tool_spans_tests` and `native_build_tests` (three refusals). Register lists per count of lent buffers are closed facts proved by cases on the count (at most three buffers fit six registers). Next: U3c, `rt` lowers `Get` and `Len` so the loop is a `runtime fn`.

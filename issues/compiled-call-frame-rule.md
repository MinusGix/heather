---
title: One frame lemma for callers of compiled code
status: closed
labels: [native,theorems,readability]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-16
updated: 2026-11-16
---

A caller of compiled code needs "what the call did not write is still there". Today that is several lemmas: `Stack::wrote_unchanged`, `wrote_resident` (`x86_64_stack.hthr`), `WroteIn` and `wrote_in_none` (`x86_64_lending.hthr`).

Wanted: one frame lemma, so that a client citing `Prog::Computes` or `Prog::ComputesOver` (`function_ir_correct.hthr`) says in one step that any predicate on memory stable under one store into the callee's room, or into a span it may write, holds after the call. Kept apart from `function_ir_correct` (in `x86_64_lending.hthr` or beside it) so it can be built in parallel with [[compiled-function-implements]].

Done when: the lemma is proved, with a probe that keeps a fact about a caller's word and about a span the callee may not write.

## Built (2026-11-16)

The rule lives beside what it speaks of:

- `lib/std/arch/x86_64/x86_64_stack.hthr`: `Stack::Stable(i, P)` (a word stored below `i` keeps `P`), the rule `Stack::wrote_frame`, the stable predicates `stable_word` and `stable_resident`, the combinators `stable_and`, `stable_given` (a fact not about memory, so a frame can speak of the entry offset) and `stable_deeper`. `Stack::Through(i, P, memory)` is the rule's conclusion held for later, and `Stack::Lends` is now `Through` at "the span reads its bytes" (same unfolding, so no load proof moved).
- `lib/std/arch/x86_64/x86_64_lending.hthr`: `Stack::StableIn(i, spans, P)` (and bytes stored into a span that may be written), the rule `Stack::wrote_in_frame`, `stable_in_and`, `stable_in_given`, `stable_in_none`, and under a `Loan` the stable predicates `Loan::stable_span`, `Loan::stable_word`, `Loan::stable_resident`, `Loan::stable_reads`.
- `lib/std/arch/x86_64/x86_64_stack_runs.hthr`, `x86_64_frame.hthr`: a body's saved registers (`Stack::stable_saved`, `Loan::stable_saved`), and the rule on a contract, `Site::returns_frame`.
- `lib/native/function_ir/function_ir_frame.hthr`: the rule over the compiler's postconditions, `Stack::callee_frame` and `Stack::answered_frame` (from the promise), `Site::callee_framed` and `Site::answered_framed` (on the contract a `Prog::Computes` or `Prog::ComputesOver` unfolds to), and `Loan::stable_buffer`. Stated over `Stack::CalleePost` and `Stack::AnsweredOver`, not over `Prog::Computes`, so reshaping the readable statements does not move it.

The predicate is an implicit argument, read off the stability proof.

Used:

- `Stack::wrote_unchanged`, `Stack::wrote_resident`, `Loan::wrote_reads`, `Loan::lends`, `Loan::unwritten_reads`, `Loan::unchanged`, `Loan::resident` and `Stack::in_memory_wrote` are each the rule at one stable predicate; their own inductions over the stores are gone.
- The call leaf (`function_ir_lower_calls.hthr`): the saved slots across a call, across a spill and across the body are the rule at `stable_saved`; `Stack::saved_unchanged` and `Stack::saved_above` are removed.
- `Target::based_left` (`native_compile_function.hthr`): "the region holds some file, the buffers not lent as they were" is proved stable and carried by the rule, in place of an induction that took each step apart.

Probes: `lib/_tests/std/arch/x86_64/x86_64_frame_tests.hthr` (a word, a word and the code, a word and an unwritten span, `Stack::Unchanged` recovered from the rule, `Lends` from a stable span, and the control `own_word_not_stable`), `lib/_tests/native/function_ir/function_ir_frame_tests.hthr` (through `Prog::Computes` and `Prog::ComputesOver`).

Not done: a written span has no ready stable predicate, since what it reads after the call is the callee's answer (`Stack::InMemory`), not a frame fact.

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

- `lib/std/arch/x86_64/x86_64_frame.hthr`: `Stack::Stable(i, P)` (a word stored below `i` keeps `P`) and `Stack::StableIn(i, spans, P)` (so do bytes stored into a span that may be written); the rule `Stack::wrote_frame`, `Stack::wrote_in_frame`, and on a contract `Site::returns_frame`. Stable predicates ready to cite: `Stack::stable_word`, `Stack::stable_resident`, `Loan::stable_word`, `Loan::stable_resident`, `Loan::stable_reads`; combined by `stable_and`, `stable_given` (a fact not about memory, so a frame can speak of the entry offset), `stable_deeper`, `stable_in_none`. The predicate is an implicit argument, read off the stability proof.
- `lib/native/function_ir/function_ir_frame.hthr`: the rule over the compiler's postconditions, `Stack::callee_frame` and `Stack::answered_frame` (from the promise), `Site::callee_framed` and `Site::answered_framed` (on the contract a `Prog::Computes` or `Prog::ComputesOver` unfolds to), and `Loan::stable_buffer`. It is stated over `Stack::CalleePost` and `Stack::AnsweredOver`, not over `Prog::Computes`, so reshaping the readable statements does not move it.
- Probes: `lib/_tests/std/arch/x86_64/x86_64_frame_tests.hthr` (a word, a word and the code, a word and an unwritten span, `Stack::Unchanged` recovered from the rule, and the control `own_word_not_stable`), `lib/_tests/native/function_ir/function_ir_frame_tests.hthr` (through `Prog::Computes` and `Prog::ComputesOver`).

Not done: the older lemmas (`wrote_unchanged`, `wrote_resident`, `Loan::unchanged`, `Loan::resident`, `Loan::unwritten_reads`) keep their own proofs and their callers; they are instances of the rule and could be restated through it. A written span has no ready stable predicate, since what it reads after the call is the callee's answer (`Stack::InMemory`), not a frame fact.

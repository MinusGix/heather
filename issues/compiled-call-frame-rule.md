---
title: One frame lemma for callers of compiled code
status: open
labels: [native,theorems,readability]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-16
updated: 2026-11-16
---

A caller of compiled code needs "what the call did not write is still there". Today that is several lemmas: `Stack::wrote_unchanged`, `wrote_resident` (`x86_64_stack.hthr`), `WroteIn` and `wrote_in_none` (`x86_64_lending.hthr`).

Wanted: one frame lemma, so that a client citing `Prog::Computes` or `Prog::ComputesOver` (`function_ir_correct.hthr`) says in one step that any predicate on memory stable under one store into the callee's room, or into a span it may write, holds after the call. Kept apart from `function_ir_correct` (in `x86_64_lending.hthr` or beside it) so it can be built in parallel with [[compiled-function-implements]].

Done when: the lemma is proved, with a probe that keeps a fact about a caller's word and about a span the callee may not write.

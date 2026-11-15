---
title: Follow-ups from the wc review: order of rounds
status: closed
labels: [native,design]
area: heather-in-heather
created: 2026-10-07
updated: 2026-10-21
---

Anchor for the follow-ups of the 2026-10-06 review of `wc` and the library
under it (at `b5b2b9d`, after [[native-wc-as-a-command]]'s C4). The review's
reading: the program is small and reads like a spec; the library's pieces
are general, but their composition is `wc`'s control flow, and the cost and
awkwardness concentrate in `lib/elf64_command.hthr` (hand-closed layout,
symbolic execution by hand) and in the trace's parallel recursions.

This issue owns only the order. Each item owns its own scope.

## Suggested order

1. [[native-label-assembler]]: labels instead of 165 hand-closed offsets;
   the producer stops mirroring the library by string.
2. [[native-straight-code-triples]], then [[native-symbolic-execution-step]]:
   one triple type with frame sets, and a step that emits the per-instruction
   proof.
3. [[command-trace-by-append]]: one homomorphism lemma per observable; the
   residue corollary is the acceptance test.
4. [[operand-command-split]]: the generic operand loop, `cat FILE...` as the
   second client.
5. Program ergonomics: [[command-bundle-ergonomics]],
   [[field-projection-sections]], [[byte-type-and-predicates]],
   [[bool-from-decidable-prop]], [[list-count-and-lines]].

Beside any of these: [[monoid-normalisation]], [[equation-rewrite-in-goal]],
and the existing [[tactic-composition-ergonomics]].

Diagnostics found while probing for this list:
[[prop-in-bool-position-reaches-kernel]],
[[width-specific-method-on-other-width]].

## Log

- 2026-10-21: Closed as not planned: the layer it is about was burned in B1 with the hand-proved native process stack (docs/native/native-program-logic-design.md §3.1, [[native-burn-process-stack]]); the last commit with it is 189659d (tag native-v0). The rebuild states programs as interaction trees and compiles them, so this per-program work does not come back in this form.

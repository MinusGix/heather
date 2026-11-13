---
title: A branch keeps only the registers its arms agree on, so a placement can lose an output
status: open
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-11
updated: 2026-11-11
---

The function compiler's code for a `Conditional` ends each arm where the
placement left it, and continues from the meet of the two arms' files
(`File::meet`, `lib/native/function_ir/function_ir_lower_structured.hthr`):
a register is known after the branch only where both arms hold the same
value in it. Nothing in the emitter brings an output to a common place. So
whether a branch's outputs survive it is the placement's to arrange, and a
placement that puts one output in different registers in the two arms
loses it; the next read of it is a refusal (`lower_program_lent` is
`None`) with no reason given.

The heuristic (`StructuredRegion::plan_in`) arranges it by picking a
target register for each output (`pick_targets`) and asking each arm's
node for that output to take it if it is free. It is not free when another
live value was put there first. Met in U3c step 3c
([[native-one-compiler]], `docs/native-one-compiler-design.md` §2.3): the
reflector writes a self-call's arguments left to right, so a loop over a
span makes its next index before it reads the byte, the tally then took
the register the next index was wanted in, and the generated loop was
refused though the hand-ordered one of step 2 was taken
(`count_early_body` beside `count_body` in
`lib/_tests/native/runtime/rt_span_loops_tests.hthr`).

## What the library does about it

A branch whose first plan loses an output read after it is planned a
second time `apart`: fresh places inside it keep clear of every register
something is wanted in, while another is free. A branch whose first plan
loses nothing keeps that plan, so no compiled code changed. This is a
second guess, not a guarantee: under register pressure the second plan can
lose an output too.

Keeping wanted registers clear everywhere, as the first and only plan, also
works and is simpler. It changes the registers of nearly every compiled
function (a straight-line body's temporaries leave RAX to the result), so
every pinned program in `crates/elab/tests/fixtures/function_ir_*` and the
checked-in `crates/linked/generated/*.s` would be rewritten. Left as a
choice for a round about the heuristic.

## The fix in the emitter

Each arm ends with moves of the branch's outputs to the targets
(`File::move_outputs`, as a function's end and a loop's back edge already
do, with `outputs_check` judging where they end), and the code after the
branch starts from the targets' file. Then any placement that keeps the
outputs alive compiles, the meet is needed only for what crosses the branch
untouched, and the placement heuristic's target requests become a way to
save moves instead of a condition of compiling. The targets would be part
of the placement (untrusted), as a loop's state registers are.

## Acceptance

- A branch with two outputs whose arms place them crosswise compiles, with
  the moves, under any placement that keeps them in registers.
- The second plan in `plan_in` is deleted.
- A refusal at a lost value says which value and where
  (the refusal reasons of `Source::refusal` do for statements; the function
  compiler's `None` says nothing).

## Log

- 2026-11-11: Filed from U3c step 3c with the second plan as the stopgap.

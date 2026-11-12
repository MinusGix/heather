---
title: The planner loses a branch's output where one arm's call makes it
status: open
labels: [native,ir,x86,planner]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-12
updated: 2026-11-12
---

Found writing the probes of a call over views (`lib/_tests/native/function_ir/function_ir_lower_views_tests.hthr`, [[native-library-exports-design]] §3.1). A branch one of whose arms ends in a call, with the call's result as the branch's output:

    Conditional(…, bit, …, Ports([word(8)]), leaf([Const(64, 8, 512)]), Call(0, [4, 5], 8))

is planned so that the function is refused: "the function's end: its result 8 is in no register". The planner picks one target register for the output (`pick_targets`, `StructuredRegion::plan_in`), which in a body that calls is never RAX (`call_pool`), the constant's arm puts 8 there, the call's arm leaves 8 in RAX, and the arms' meet keeps neither. Written with a fresh result and a move after the call (`Compose(Call(0, [4, 5], 9), leaf([Move(64, 8, 9)]))`) it lowers, which is what the probes do and what `rt`'s generator emits.

The function is fine and the placement is not, as in [[function-ir-planner-register-pressure]]. Two ways, either in the planner alone (untrusted search, so no theorem moves):

- where an arm's last leaf is a call (or a call over views) whose result is an output, take RAX as that output's target in both arms, when nothing else wanted there crosses the branch;
- or leave the plan and have the arm's file answer a `Move` the planner inserts.

The first changes no code for programs that lower today.

## Done when

The branch above lowers as written, in `function_ir_lower_views_tests.hthr` or beside the planner's probes, and `scripts/linked --check` shows no generated file moved.

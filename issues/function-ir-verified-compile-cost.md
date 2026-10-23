---
title: State the verified lowering's equation per function as programs grow
status: open
labels: [native,ir,proofs,perf]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-23
updated: 2026-10-23
---

`compile-x86`'s certificate ([[function-ir-verified-lowering]] round 4)
checks `lower_program(p, plan_program(p)) = Some(code)` by `refl` in one
declaration. Every declaration has the same fuel, so that one evaluation of
the planner and the lowering bounds the program size the path accepts. A
three-function example (`examples/x86-native/program.hthr`) already spends a
sizable fraction of it. Everything after it evaluates the literal `code`, and
the bytes go in pieces, so `lowers` is the one statement that grows with
the whole program.

What would fix it: per-function statements. `emit_functions` lowers one
function at a time onto the code before it. A lemma that unfolds one step
of it would let function `k`'s lowering be its own declaration, over the
literal code of functions `0..k`, glued together the way the bytes are.
Before that, measure whether the planner or the emitter dominates
(`--item-timings`, `steps`). A planner that dominates could instead be
stated as a literal placement, since the theorem holds for every
placement.

Not urgent: no program the CLI compiles today is near the limit.

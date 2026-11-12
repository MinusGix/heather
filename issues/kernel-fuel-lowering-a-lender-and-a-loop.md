---
title: The kernel runs out of fuel checking that a lender and a loop lower together
status: open
labels: [native,ir,kernel,probes]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-12
updated: 2026-11-12
---

A probe cannot state that the function compiler accepts a two-function program of a lender and a loop:

```heather
theorem xor_window_lowers(): lower_program_lent(xor_window::program, plan_program(xor_window::program),
    program_counts(xor_window::program)).is_some() = True { refl }
// error: the kernel rejected `xor_window_lowers`: OutOfFuel
```

(`lib/_tests/native/runtime/runtime_span_lend_tests.hthr`, [[source-buffers-as-views]]; the theorem is left out there with a note.) The elaborator's evaluator answers `True`, and the refusal mirror says the function is not refused. The same statement checks for each half alone (`xor_from_lowers` in `runtime_span_reads_tests.hthr`; `copy_window_lowers` in the same file, whose callee is no loop), and for `copy_span_program()`, a loop and nothing else. `.IsTrue() { trivial }` fails the same way.

It is no obstacle to compiling: `heather compile-x86` checks the lowering a piece at a time (`lower_program_lent_emitted`, "no one statement evaluates more of the code than a piece"), and the export of this shape (`copy_window`) is certified in seconds. What it costs is a probe's cheapest sentence about a program, at a size a real program passes quickly.

## Ways

- Find what the kernel spends here that the elaborator's evaluator does not. The planner (`plan_program`) and the lowering each walk the region with lists keyed by id (`function-ir-scan-id-cost` is the known linear scan); a lender's views add checks keyed by port.
- A probe-side statement by pieces: the mirror's answer (`Function::refused(…) = "nothing: …"`) per function is cheaper than the code, and would say the same.
- A fuel knob for a test module is the wrong fix: the budget is what keeps a runaway check from taking the machine.

## Done when

The theorem above checks in `runtime_span_lend_tests.hthr`, or the file states acceptance another way that does.

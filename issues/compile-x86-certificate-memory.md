---
title: compile-x86 runs out of memory on a deep conditional chain or a several-function program
status: open
labels: [native,compiler,performance]
area: heather-in-heather
milestone: [nh-front,self-lexer]
created: 2026-11-10
updated: 2026-11-10
---

`heather compile-x86` runs out of memory or fuel on functions well inside
what the generator and the linking accept. Found certifying the scanner's
automaton (`lib/lang/lexer/lexer_scan.hthr`); all runs on the cloud box
under the usual 8 GiB cap.

| shape | what happened |
|---|---|
| one function, an 18-arm `else if` chain (so 18 levels of nesting), each arm a constant | memory allocation failed inside `evaluate_numbers` |
| a program of four functions, about 200 mentions together | the same |
| one function of 21 arms, each a short chain of byte tests (`step_symbols` before it was split) | `…_native_scanned_0: OutOfFuel`, which is [[function-ir-scan-id-cost]] |
| one function of about 16 arms, about 12 levels deep | certifies, in tens of seconds |

The fuel case is the scan's known cost and belongs to that issue. The
memory case is new and not attributed: `evaluate_numbers`
(`crates/elab/src/function_ir_source/program.rs`) evaluates a closed list of
numbers through the kernel, and a deep conditional chain or a second
function takes it from comfortable to past 8 GiB with nothing in between
measured. Candidates, none checked: the laid-out code's offsets computed
per block by re-walking the chain (quadratic in depth, with the
intermediate lists retained); the evaluator's force cache holding every
intermediate assembly of a nested region; or a literal spine past the long
literal cap.

What it costs today: a function is kept to about sixteen arms and twelve
levels, so a table-shaped function (a scanner's transitions, a
classifier) is cut into families by hand, each its own program. The same
round's [[runtime-generator-program-size]] is the linking side of the same
limit.

## Done when

The memory is attributed (a `--timings` run with the allocation counters,
or `scripts/bench-probes` cases at 8, 16 and 24 arms), and either a
24-arm chain certifies under the cap or the reason it cannot is written
here with the shape that does.

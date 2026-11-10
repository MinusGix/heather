---
title: compile-x86 runs out of memory on a deep conditional chain or a several-function program
status: closed
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

## Log

- 2026-11-10: Attributed and fixed. None of the three candidates above was the cause; there were four, each found by measuring the one before it away.

  1. **The placement planner recomputed its `let`s.** `plan_block` and `plan_from` (`function_ir_lower_structured.hthr`) read a `let`-bound plan at several places, and the kernel computes a `let` again at each ([[elaborated-let-sharing-lost]]), so a chain of conditionals replanned its tail at every level. A per-definition count of unfoldings in the read showed it; they bind with `shared` now. A 16-arm chain's placement read went from 6.7M evaluator steps to 0.76M. The placements are the same: every other export's bytes are unchanged.
  2. **Each read evaluated the whole program.** `evaluate_numbers` evaluates in a fresh arena, and the placement, the code, the layout and the bytes were each read as one value of the whole program. The compiler now reads a function at a time, each from the literals the reads before it gave, so memory follows the largest function.
  3. **Layout and bytes walked the program per label.** `Prog::laid_out` and `assemble` find a label by walking the code. `compile-x86` now reads and states both through the label table `write-elf` has used since [[native-compile-linear-layout]] (`crates/cli/src/native/labels.rs`, `x86_64_asm_table.hthr`).
  4. **A caller's scan statement forced its callees' code.** `program_scan` read a callee's arity off its parameter list, which is its lowered code. The scan is against a list of arities now (`program_scan_at`), each function checking its own entry.

  Measured on the cloud box under the 8 GiB cap: the 16-arm chain's peak fell from about 2.5 GB to under 1 GB; a 24-arm chain certifies in about seven seconds at about 1.1 GB, where it died; the scanner's whole automaton (`scan_step`, twenty-six functions, about fifteen thousand bytes) certifies in well under a minute at under 2 GB. That meets the done-when.

  What bounds a single function now is its emission statement and the memory of its own reads, filed as [[native-function-emission-one-statement]].

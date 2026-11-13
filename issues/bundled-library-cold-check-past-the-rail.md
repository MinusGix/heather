---
title: One inline-composed theorem made the bundled library's cold check pass the suite's rail, and nothing said so
status: open
labels: [native,performance,proofs,testing]
area: heather-in-heather
created: 2026-11-12
updated: 2026-11-12
---

`scripts/test --pr` stopped in its warm-up on 2026-11-12, before any test ran: `native::tests::the_bundled_library_checks` (the bundled proof library checked in one process of the test binary, under the suite's 6 GiB address-space rail) died with `memory allocation of … bytes failed` in the kernel's typing memo. The round had edited `crates/syntax`, so no image of the bundled library was this build's and the library was checked cold. The rounds before it had edited only `lib/`, and replayed.

## What it was

One theorem. `function_ir_lower_calls::function_runs` (a compiled function's whole run: the entry and saves, the body and the result's moves, the reloads and the frame freed) was written two rounds earlier, with the callee-saved registers, as one proof composing its three stages inline: each stage's witness a `let` over the application before it, and every later statement holding those. Measured cold at kernel width one, release binary: that one declaration was most of the whole closure's time and nearly all of its conversion queries. In the test binary the module reserved a little over 6 GiB of address space, in arenas of a gibibyte, so the same tree passed or failed by which side of the sixth arena a run fell: the round that wrote the theorem passed.

`docs/proof-patterns.md` §2 has the rule ("split a long proof into stage theorems with written statements") and the proof broke it.

## What was done

`function_runs` is three theorems, each at the state it starts from: `function_enters` (as before), `function_runs_saved` and `function_closes`, with `function_runs` their composition. The three together cost about what any other theorem of the module does. The bundled library's cold check in the test binary is back to a fraction of the rail in address space, resident memory and time.

## What is left

- **Nothing said so.** A declaration can become most of a module's cost and no lane reports it while the images replay: the PR lane's timings are over replayed images, `scripts/bench --check` holds the kernel's benchmarks, and the diary (`scripts/perf report`) is read when choosing a perf target, not at the end of a round. To do: the warm-up (or the library gate) prints the declarations past some share of their module's kernel time when it does check cold, and a round that adds to `lib/native/function_ir` or `lib/std/arch/x86_64` reads `--timings` for the module it changed (a line for CLAUDE.md once the first half exists).
- **The other inline compositions.** `function_runs` was the worst and may not be the only one: the same `--timings` run lists `function_body` and `SpanSet::any_cut_all` next, each small beside it. Worth one pass over the top of the table after the next large native round.
- **The rail is on address space and the allocator reserves by the gibibyte**, so a process near the rail fails or passes by arena, not by use. Recorded here; not to be changed for this.

Related: [[native-certificate-whole-program-evaluations]], [[runtime-generator-link-cost]].

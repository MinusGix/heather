---
title: compile-x86 maps twice what it holds: the 8 GiB rail is met on the allocator's reservations
status: open
labels: [native,compiler,performance]
area: heather-in-heather
created: 2026-11-14
updated: 2026-11-14
---

`heather compile-x86` on the linked SHA-256 compression maps about twice
the memory it holds, so the 8 GiB address-space rail (`ulimit -v`, which
`scripts/linked`, `scripts/bench-native` and the suite all run it under) is
met well before the memory is used. Found when `scripts/bench-native`'s
cold compile of `sha256_compress` died at the rail with a failed allocation
inside `evaluate_numbers` while the process held less than 5 GiB.

Measured on the cloud box, a fresh `--cache-dir`, sampling
`/proc/<pid>/status`:

| | peak mapped (`VmPeak`) | peak resident (`VmHWM`) |
|---|---|---|
| before the fix below | past 8 GiB (killed) | 4.7 GiB at the kill |
| after it | 7.3 GiB | 3.5 to 3.9 GiB |
| after it, `MIMALLOC_ARENA_RESERVE=131072` (128 MiB) | 6.6 GiB | 3.9 GiB |

The mapped size climbs in steps of exactly 1 GiB and never comes down:
mimalloc reserves address space an arena at a time and keeps a reservation
after what was in it is freed. Each read's value arena is freed when the
read ends (`with_reads`), and the resident size does fall back between
reads; the mapped size does not.

## What was fixed (PR #622)

The largest read was not a computation. A search's answer was spelled as
decimal text in Heather, and a decimal digit there is a long division, a
step for each bit of the number: the K table's function took ten million
evaluator steps to spell, against a few hundred thousand to find. A
spelling is now numbers, each a character's code or a mark and a number the
compiler writes in decimal itself (`lib/native/function_ir/function_ir_spelled.hthr`).

`HEATHER_READ_TRACE=1` makes `compile-x86` report each read's evaluator
steps, time, and the process's peak resident and mapped memory during it,
which is how the read was found.

## After the optimizer's step 4 (2026-11-14)

A function tested at its entry is larger (its plain arm, and the tested
arm with its inlined callees), and the largest function's planning grew
with it. Same measurement, cold store:

| | peak mapped | peak resident |
|---|---|---|
| the test put after inlining (the inlined body twice) | past 8 GiB (killed in `…_opt_taken_9`); 9.4 GiB under a 14 GiB rail, and `…_emits_9` then ran out of the kernel's fuel | 5.3 GiB |
| the test put first (the plain arm is the function as written) | 7.96 GiB | 4.3 to 4.5 GiB |

So the compile fits the rail with about 0.2 GiB to spare. The two largest
reads are still the planner's on function 9, `…_opt_taken_tested_9` and
`…_plan_9`, about seven and six million steps.

What was ruled out: a branch planning itself again when it loses an output
(`StructuredRegion::plan_in`). Planning only the outermost such branch
again gave the same steps and the same code, so no function here pays for
that. What the read trace shows instead is the planner's steps a node
growing with the function's size (a few thousand a node in a function of
compares and constants, tens of thousands in the function with the most
inlined), which points at what the planner asks of the lowering's file at
every node (`File::known` is a list, scanned), not at the planner's own
passes: the reads of a function's continuation at every `Compose` were
measured at under a third of the planning.

## What is left

- ~~The planner runs twice on every function the optimizer keeps~~: done
  2026-11-14, the lowering's question answers its placement.

- The margin under the rail is still thin (about 0.7 GiB of address space
  on this program), and it is the allocator's reservations, not use. A
  smaller arena reservation recovers some of it; so might returning a
  read's arena to the system when the read ends. Neither is tried beyond
  the one environment-variable run above.
- The largest reads now are the planner's: `…_opt_taken_9` (whether the
  lowering takes a function with the planner's placement) and `…_plan_9`,
  about five million steps each on the function with the most inlined into
  it, each a gigabyte resident while it runs.
- The elaborated library the compile starts from is itself about 2.9 GiB
  resident on a cold store.

## glibc's thread arenas (2026-11-14, thread "Cut the warm compile's cost")

On the tree with the word load (PR #622's branch), cold store, release
binary, `VmPeak` sampled every half second, `/proc/<pid>/maps` read during
the optimizer's reads:

| mapped | what |
|---|---|
| 5 × 1 GiB | mimalloc's arenas |
| 16 × 64 MiB | glibc `malloc` arenas, one a thread, almost all of each reserved and never touched |
| 16 × 8 MiB | thread stacks |

Rust's allocations all go to mimalloc, but glibc `calloc`s a record for
each thread-local destructor a thread registers, and a thread's first
`malloc` makes it a 64 MiB arena of its own. `heather` now runs itself
again with `MALLOC_ARENA_MAX=1` where that is unset (`one_malloc_arena`
in `crates/cli/src/main.rs`; `mallopt` would be `unsafe`, which the
workspace forbids, and glibc reads the variable only at start), for every
command, since the suite's 6 GiB rail meets the same reservations.

| `sha256_compress`, cold | wall | peak mapped | peak resident |
|---|---|---|---|
| before | 261 s | 6.3 GiB | 4.4 GiB |
| one glibc arena | 258 s | 5.3 GiB | 4.4 GiB |
| one glibc arena, mimalloc arenas of 256 MiB (`MIMALLOC_ARENA_RESERVE`) | 243 s | 5.5 GiB | 4.3 GiB |

A smaller mimalloc reservation does not help: past eight arenas mimalloc
doubles the size of every eighth one, so many small arenas end larger. The
7.96 GiB above was measured before the word load; on this tree the peak is
6.3 GiB, and 5.3 GiB with the fix, 2.7 GiB under the rail.

Planning twice is gone (see [[optimizer-search-answers-memo]]): the
lowering's question answers its placement and that is the program's. The
two largest reads are still one function's planning and emission, about
the same steps as before, so the resident peak is unchanged.

### Where a cold compile goes

Same box, `--timings`, cold store (353 s with the timing on and a build
beside it; the shape is what matters):

| | share |
|---|---|
| elaborating the library the compile imports (120 modules; `function_ir_lower_calls` alone 56 s, `runtime` 17 s, the SHA-256 modules about 48 s together) | about two thirds |
| the optimizer's and the lowering's reads (398 evaluations, 106 M steps) | about 47 s |
| elaborating the probe modules those reads stand on (each made function is a literal) | about 30 s |
| the certificate | 23 s |

A warm store takes the first and last away (image replay), and now the
middle two.

## Log

- 2026-11-14: The time side of the optimizer's reads is its own issue: [[optimizer-search-answers-memo]] (a warm compile evaluates every search again; remembering an answer is safe because the certificate checks what it made).

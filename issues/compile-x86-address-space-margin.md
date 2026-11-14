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

## What is left

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

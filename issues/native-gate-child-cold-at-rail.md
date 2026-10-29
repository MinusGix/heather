---
title: The library gate's lib/native child is at the 300 CPU-s rail again from a cold store
status: open
labels: [testing,performance,native,images]
area: infrastructure
created: 2026-10-29
updated: 2026-10-29
---

[[library-gate-native-cold-rail]] (closed 2026-10-27) brought the gate's
`lib/native` child under the rail by making module images DAGs. On master
709e71c, a cold run of the gate's own command for that folder (`heather
check --cache --expectations --world lib lib/native`, kernel width one, the
dev binary, a 4-CPU cloud box, run after the `lib/std/*` folders had built
the shared prefix) took 299 s user plus 3 s system. That is just over the
suite's `ulimit -t 300`, which counts both. The run was made with a looser
rail, so it finished; under the suite's it would have been killed.

Where it goes (cold module totals, `perf/bench/targets.md` T4): the
`native_compile_*` modules and `function_ir_lower_calls`, mostly kernel.
The two heaviest declarations reproduce alone ([[native-lemma-kernel-steps]]).
Several others are cheap alone and costly cold, because the cold gate charges
the module's shared generated items to their first user
(`docs/cloud-benchmarks.md` §3).

The order here was not quite the gate's: the gate sorts folders by the
world's order, and this run built the prefix in `lib/std/arch`'s child. The
`lib/native` child's own modules are most of its time either way.

## Done when

A cold gate on a fresh cloud box (the sentinel's configuration) leaves the
`lib/native` child with a margin under the rail, read off the sentinel's
per-target times or a by-hand cold folder run like the one above.

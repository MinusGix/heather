---
title: The runtime fn generator's cost grows with the functions a program links, near the native gate's rail
status: open
labels: [native, runtime-fn, performance]
area: heather-in-heather
milestone: [hih-native-heather]
created: 2026-11-06
updated: 2026-11-06
---

Found wiring loops into `runtime fn` (design §16.11). `loop_anywhere.hthr`
as first written (seven runtime fns: two fuel loops at a closed and an open
count, a loop calling a loop, a `Bool` helper) took about 280 CPU-s to
compile cold beyond the warmed runtime closure, against the 300 s rail
`native_program`'s children run under. A `--timings` run attributes it to
the elaborator running the generator, not the kernel gate: `anywhere`'s own
`runtime fn` declaration took about 180 s (gate about 3 s), and each callee
10 to 30 s. Cutting the example to five functions (its closed-count call is
`loop_settle`'s and `loop_multiply`'s already) brought it to about 160 s.

Where the time goes inside the generator is not yet measured: the linking
(`runtime_linked`, every callee's instance and sources re-read per caller)
and the published statements' elaboration (`infer(built)` on the instance)
are the candidates. A tool-sized runtime program would meet this first.

---
title: The native sort gate is killed at the suite's rail on a fresh box
status: open
labels: [native,testing,perf]
area: infrastructure
created: 2026-11-03
updated: 2026-11-03
---

`compiled_sort_runs_as_gnu_sort` (crates/cli/tests/native_tools.rs) was killed twice on a fresh cloud box on 2026-11-03, under both `scripts/test -p heather-cli --test native_tools` and `scripts/test --pr`. Both times it died silently while checking the certificate ("checking `sort_tool`'s compile and its 12893 bytes in …"), which is how a run at the CPU rail ends. The other twelve tools pass.

This is not a regression of the branch it was seen on (bool-conditions-and-literals). Master's binary (0cf4ea2) and the branch's binary wrote byte-identical `sort` ELFs and certificates, at the same width-one CPU cost: about 26 minutes cold through `write-elf` with an empty image cache. Most of that is building the closure's images, and the share that falls inside the test's per-process rail was not measured.

Next step: time the certificate check alone over warm images (`--timings` on the write-elf, `scripts/bench-probes --heavy`) and see whether it fits the rail at width one. If it doesn't, either make sort's loop bodies cheaper (see the liveness cost in [[native-write-elf-join-liveness]]) or give this gate its own rail the way the other heavy gates have one.

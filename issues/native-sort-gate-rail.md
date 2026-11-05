---
title: The native sort gate is killed at the suite's rail on a fresh box
status: open
labels: [native,testing,perf]
area: infrastructure
created: 2026-11-03
updated: 2026-11-04
---

`compiled_sort_runs_as_gnu_sort` (crates/cli/tests/native_tools.rs) was killed twice on a fresh cloud box on 2026-11-03, under both `scripts/test -p heather-cli --test native_tools` and `scripts/test --pr`. Both times it died silently while checking the certificate ("checking `sort_tool`'s compile and its 12893 bytes in …"), which is how a run at the CPU rail ends. The other twelve tools pass.

This is not a regression of the branch it was seen on (bool-conditions-and-literals). Master's binary (0cf4ea2) and the branch's binary wrote byte-identical `sort` ELFs and certificates, at the same width-one CPU cost: about 26 minutes cold through `write-elf` with an empty image cache. Most of that is building the closure's images, and the share that falls inside the test's per-process rail was not measured.

Next step: time the certificate check alone over warm images (`--timings` on the write-elf, `scripts/bench-probes --heavy`) and see whether it fits the rail at width one. If it doesn't, either make sort's loop bodies cheaper (see the liveness cost in [[native-write-elf-join-liveness]]) or give this gate its own rail the way the other heavy gates have one.

## Log

**2026-11-04.** Measured over warm images at width one with `--timings`,
beside one other run on a 4-core cloud box: `write-elf lib/native/native_heap_tools.hthr
sort_tool` costs 323 CPU-s at `4c1b702` and 348 at `b037918` (the debug-profile
binary the test runs: 300), with byte-identical ELFs. About 150 s is the
certificate modules (`sort_tool_elf_*`), about 30–80 s replaying the closure,
and the rest is outside any item row (the compile by kernel evaluation). tac
fails the same way in a cold suite, at 304 s. So the gate cannot fit the rail
at width one; [[master-red-2026-11-03]] and [[master-red-2026-11-04]] were this.

native_cat and native_tools now run under a 900 s CPU rail (`CPU_RAIL_OVERRIDES`
in `scripts/run-test-targets.mjs`, and the focused path in `scripts/test`).
This issue stays open for the other half: make sort's and tac's certificates
cheaper, then drop the override. Under the override `scripts/test -p
heather-cli --test native_tools` passes 14/14.
- 2026-11-05: gardener: cites a file it shares with [[native-tool-test-cold-certificate-rail]] (`crates/cli/tests/native_tools.rs`); [[runtime-fn-arena-lists]] (`crates/cli/tests/native_tools.rs`).

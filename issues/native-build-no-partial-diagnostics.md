---
title: A build killed at the CPU rail leaves no timings and no certificate
status: open
labels: [native, tooling, perf]
code: crates/cli/src/native.rs @ 357c0afa
created: 2026-09-29
updated: 2026-09-29
---

`build-x86` writes `--timings` and the certificate only when the check
returns. A refused certificate is fine (the table is written before the error
is reported), but a build killed by `ulimit -t` leaves nothing, and a
certificate that fails to parse is reported by line and column in a file
that was never written.

Found in the `wc` round (docs/native-wc-design.md §6.1): one declaration
ran for 20+ CPU-minutes, and finding it took a temporary hook that dumped the
certificate (`HEATHER_DEBUG_CERT`) and cut it at a marker
(`HEATHER_DEBUG_CUT`), then bisecting by rebuilds. Both were removed before
committing.

Shape of a fix: write the certificate before checking it (to a sibling path
that is not the published one), and stream timing rows as declarations
finish, or on SIGXCPU, so the last row names the one that was running.
Related: [[closed-length-facts-evaluate-encodings]], what the bisection found.

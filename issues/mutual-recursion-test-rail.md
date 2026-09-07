---
title: Keep mutual recursion acceptance inside the parallel suite resource rail
status: open
labels: [testing,performance,elaboration]
created: 2026-09-07
updated: 2026-09-07
---



During validation of [[x86-native-export]], the plain full `scripts/test`
completed with 2453 passing tests and no assertion failures, but the
`mutual_recursion` target ended with SIGKILL after 12 progress dots and no
result line (160.48 s target wall time, six-way runner). The suite correctly
reported INCOMPLETE. An immediate isolated rerun through
`scripts/test -p heather-elab --test mutual_recursion -- --nocapture`
passed all 13 tests in 90.41 s. The x86/CLI change did not modify this target
or its elaborator/kernel dependencies.

Investigate the bounded parallel-run resource failure. `base()` in
`crates/elab/tests/mutual_recursion.rs` currently elaborates the same nine
library modules, through `omega`, afresh for every case. The existing
kernel-rechecked semantic test-image helper is a candidate for avoiding
repeated fixture work without weakening checks on new mutual-recursion
examples. Identify whether remaining workload needs a split process rail.

Acceptance: all cases run in the ordinary parallel full suite without
weakening limits or losing literal, neutral, polymorphic, and refusal cases.
[[mutual-recursion-declarations]] owns the language behavior being tested.

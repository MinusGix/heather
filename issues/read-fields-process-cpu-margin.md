---
title: read_fields_process sits closest to the per-test CPU limit; load alone can cross it
status: closed
labels: [perf,test]
area: infrastructure
created: 2026-09-30
updated: 2026-10-21
---

The elab test `read_fields_process` (wc's three-field process: field_line, elf64_read_fields, the record loop and its claim) runs at 215-260 CPU-s against the suite's 300 CPU-s per-process limit (scripts/test). On 2026-09-30, during native-architecture-review R7, one full suite at a load average near 16 (other sessions) killed it at 296 CPU-s. The same commit passed alone and in the next full suite (257 CPU-s). R7 added a few percent of work to elf64_read_fields' check (steps +2.4%, misses +4%, `scripts/timings --diff`); every process test ran about a quarter slower in that loaded run.

What dominates: `elf64_read_fields::field_prints` (~2-4 s wall of gate, counts unchanged by R7; see issues/field-prints-gate-after-lowering-round.md) and field_line's place-value lemmas (`field_place_step`, `FieldGroupFacts`, `high_group_rooms`). Levers: split the test's three tests into processes of their own (field_line_format already splits its two words for this reason), or reduce field_prints' gate per the other issue.

## Log

- 2026-10-03: 2026-10-03, full `scripts/test` at the goal-world fix (PR #2), 4-core cloud box, cold images: `read_fields_process` ran in 85.9 CPU-s, 29% of its rail, and is no longer the closest member to the rail. The closest is now `native_wc` at 198.0 CPU-s (66%), then `native_filter` (148.4) and `filter_step_generation` (133.4). The fix is not why the number dropped: `scripts/perf ab` on `lib/elf64_read_fields.hthr` showed no change, and `field_prints`' gate is the same within noise. The difference from the 215–260 measured on 2026-09-30 has not been attributed to a commit (other rounds landed since, and the machines differ). Left open for one same-machine reading on the desktop before closing.
- 2026-10-21: Closed as not planned: the layer it is about was burned in B1 with the hand-proved native process stack (docs/native/native-program-logic-design.md §3.1, [[native-burn-process-stack]]); the last commit with it is 189659d (tag native-v0). The rebuild states programs as interaction trees and compiles them, so this per-program work does not come back in this form.

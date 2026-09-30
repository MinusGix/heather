---
title: read_fields_process sits closest to the per-test CPU limit; load alone can cross it
status: open
labels: [perf,test]
created: 2026-09-30
updated: 2026-09-30
---

The elab test `read_fields_process` (wc's three-field process: field_line, elf64_read_fields, the record loop and its claim) runs at 215-260 CPU-s against the suite's 300 CPU-s per-process limit (scripts/test). On 2026-09-30, during native-architecture-review R7, one full suite at a load average near 16 (other sessions) killed it at 296 CPU-s. The same commit passed alone and in the next full suite (257 CPU-s). R7 added a few percent of work to elf64_read_fields' check (steps +2.4%, misses +4%, `scripts/timings --diff`); every process test ran about a quarter slower in that loaded run.

What dominates: `elf64_read_fields::field_prints` (~2-4 s wall of gate, counts unchanged by R7; see issues/field-prints-gate-after-lowering-round.md) and field_line's place-value lemmas (`field_place_step`, `FieldGroupFacts`, `high_group_rooms`). Levers: split the test's three tests into processes of their own (field_line_format already splits its two words for this reason), or reduce field_prints' gate per the other issue.

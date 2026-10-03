---
title: One-armed structured branch (CodeWhen) drops the jump over an empty arm
status: open
labels: [x86,codegen]
created: 2026-09-30
updated: 2026-09-30
---

A passthrough arm is empty since the `Move` node (docs/structured-lowering-code-size-design.md §3.2), but `CodeBranch` still lays it out as `cmp ; jae +2 ; jmp join`. A one-armed `CodeWhen(test, displacement, body)` (design §2.3) would be `cmp ; jb join`, which is 2 bytes a step (20 steps in `field_low`, 30 in `field_high`).

The cost is a new `StructuredCode` constructor carried through every fold over it: `structured_bytes`, `structured_after`, `ExecuteStructured`, `StructuredLayout`, `StructuredDecodes`, the branch property, cases and read lemmas in `x86_64_structured_block`, the fetched-execution fold in `x86_64_fetched_code`, the access-memory fold, and the certificate generator's branch emission (`structured_cert.rs`). It was deferred when the round met its acceptance without it (design §8).

---
title: One-armed structured branch (CodeWhen) drops the jump over an empty arm
status: closed
labels: [x86,codegen]
created: 2026-09-30
updated: 2026-10-13
---

A passthrough arm is empty since the `Move` node (docs/archive/structured-lowering-code-size-design.md §3.2), but `CodeBranch` still lays it out as `cmp ; jae +2 ; jmp join`. A one-armed `CodeWhen(test, displacement, body)` (design §2.3) would be `cmp ; jb join`, which is 2 bytes a step (20 steps in `field_low`, 30 in `field_high`).

The cost is a new `StructuredCode` constructor carried through every fold over it: `structured_bytes`, `structured_after`, `ExecuteStructured`, `StructuredLayout`, `StructuredDecodes`, the branch property, cases and read lemmas in `x86_64_structured_block`, the fetched-execution fold in `x86_64_fetched_code`, the access-memory fold, and the certificate generator's branch emission (`structured_cert.rs`). It was deferred when the round met its acceptance without it (design §8).

## Log

- 2026-10-13: Landed 2026-10-13 (docs/archive/structured-lowering-code-size-design.md §2.6): CodeWhen(test, rel8, body), short form only; an empty true arm takes the false arm as body under the negated comparison, a NonZero test keeps both arms. The empty arm is no certificate node, so a place is five nodes: field_high 7,234 → 6,126 declarations, standalone check 16.3–16.5 → 13.9–14.7 s; field_low 10.7–11.4 → 9.9–10.1 s; bytes 868 → 808 and 637 → 597.

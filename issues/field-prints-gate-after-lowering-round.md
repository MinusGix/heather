---
title: field_prints' kernel gate grew across the structured-lowering round
status: open
labels: [perf]
area: infrastructure
created: 2026-09-30
updated: 2026-09-30
---

`scripts/perf ab --base 08d77938 --whole-tree` on the `wc` build, across the structured-lowering round, moved every counter down by 14–21% (declarations gated, evaluator steps, conversion misses). One library item went the other way, separately in all samples: `elf64_read_fields::field_prints`, whose kernel gate grew by about a quarter. It is a theorem over open `StructuredCode` (`low`, `high`), so its cost tracks the library's definitions, not the generated code. Candidates are the `JumpIf` / `ConditionCode` family replacing the jump constructors, `CodeBranch` over `BranchTest`, and `branch_test_state` as a record literal.

Next step: `--timings` on `elf64_read_fields` at both commits, then `scripts/timings --diff` on that item.

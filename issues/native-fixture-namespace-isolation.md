---
title: Isolate native integration artifacts across sandbox process namespaces
status: closed
labels: [testing,x86]
created: 2026-09-20
updated: 2026-09-20
---

## Scope

Native integration fixture paths that use only the process ID are not unique
across sandbox process namespaces. Overlapping suite runs can address the same
output directory, causing publication to refuse existing files or one fixture
to remove another's artifacts.

The shared `native_support::Built` helper now includes a nanosecond nonce, as
the buffer cursor/scanner tests already do. The two direct artifact paths in
`crates/cli/tests/native.rs` still use only process IDs and need the same
isolation review.

## Acceptance

- Give the remaining native integration outputs unique per-run names.
- Keep each test's cleanup confined to its own artifacts.
- Validate publication/refusal behavior and a plain full suite.

## Context

Discovered while validating [[x86-buffer-scan-loop-refinement]]. The scanner
proof changes do not rely on process IDs or host fixture naming.

## Log

- 2026-09-20: Added per-run nonces to the shared Built helper and both direct native/ELF integration output directories. Existing cleanup remains scoped to each returned directory. Final full-suite validation is pending.
- 2026-09-20: Confirmed in the preceding full run: the multiple-live-stack-slots target failed because target/native-multi-stack-save-146/caller already existed, while 2834 tests passed (including both scanner tests). That run started before the nonce fix. A final plain suite including the fix is in progress.
- 2026-09-20: Final plain scripts/test including all nonce changes passed: 2835 passed, 0 failed, 5 ignored. The shared native helper, direct assembly integration output, and direct ELF integration output now have distinct per-run directories, and cleanup stays scoped to those directories.

---
title: Report test-target outcomes immediately while retaining grouped logs
status: closed
labels: [tooling,testing,diagnostics]
created: 2026-09-08
updated: 2026-09-28
---

`scripts/run-test-targets.mjs` buffers each target's output and prints full
blocks after all scheduled targets finish. Its immediate `[done]` line reports
only duration. A long keep-going suite therefore withholds the actual outcome
of an expensive native target while many unrelated tests continue. This delays
failure diagnosis and makes a completed target easy to mistake for a pass.

## Acceptance

- Immediate target-completion messages distinguish pass, assertion failure,
  signal/resource termination, and missing/incomplete result summaries.
- Show a bounded useful failure excerpt or a discoverable per-target log as
  soon as it is available; preserve the final grouped logs and suite totals.
- Keep concurrent output legible and test the formatting/classification in the
  existing Node runner tests, including killed children and truncated output.
- Do not change keep-going behavior, caps, or what counts as suite completion.

## What it assumes from elsewhere

- [[generated-proof-cost-diagnostics]] owns checker-level attribution; this issue
  owns delivery of test outcomes already available to the runner.

## Log

- 2026-09-28: LANDED: completion messages now distinguish PASS, FAIL, TERMINATED (with signal), and INCOMPLETE (with exit status and summary count), retaining wall/CPU timings. Failures print up to eight excerpt lines, capped at 160 characters each, in the same write as the completion; output truncation is explicit. Final grouped output, accounting, rails and scheduling policy are unchanged. The Node runner tests cover outcome classification, excerpt bounds, killed children, truncated output, reporting while another target remains active, keep-going and fail-fast. Validation: 13 Node tests passed. Final plain `scripts/test`: 3,025 passed, 0 failed, 5 ignored.

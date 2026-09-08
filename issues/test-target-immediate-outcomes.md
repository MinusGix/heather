---
title: Report test-target outcomes immediately while retaining grouped logs
status: open
labels: [tooling,testing,diagnostics]
created: 2026-09-08
updated: 2026-09-08
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

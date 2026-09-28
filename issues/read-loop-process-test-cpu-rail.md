---
title: Read-loop process mutation controls exceed their CPU rail
status: open
labels: [testing,x86,performance]
created: 2026-09-28
updated: 2026-09-28
---

The `read_loop_process` member of `family_function_ir` runs three tests under
one `scripts/test` process's 300 CPU-second rail. The group is SIGKILLed
before completing its summary, so the full suite correctly reads INCOMPLETE.

Observed while verifying [[closed-nat-equality-depth-budget]], with unchanged
library sources and caps. Running the group after temporarily restoring the
old `conv.rs` also dies at the same rail, so this predates that kernel fix.
The Nat issue owns its conversion change; this issue owns the test grouping
and the margin needed to run all read-loop library, fetched-execution and
mutation controls in an ordinary full suite.

The current group is `crates/elab/tests/read_loop_process.rs`:
`read_loop_library_checks`, `counting_loop_runs_fetched`, and
`slow_acceptance_read_loop_refusals`. Its shared fixture also re-elaborates
the read-loop dependency suffix. Sharing only that prefix via the existing
checked semantic-image fixture still did not let the combined group finish;
that experiment was reverted. The isolated `slow_acceptance_read_loop_refusals` test also dies under the
same runner/caps, so splitting just the other two tests away is insufficient.

The existing print-refusal file is a precedent for separating expensive
controls into their own capped process. Do not increase the rail or skip
mutation coverage to hide the incomplete result.

## Acceptance

- Plain full `scripts/test` runs every existing read-loop control and reaches
  a complete result under the existing rail.
- Any prefix reuse returns `NoGate`, so test-specific libraries, certificates
  and mutations continue to reach the real kernel.

## Log

- 2026-09-28: Final verification of [[closed-nat-equality-depth-budget]]: full suite
  INCOMPLETE (3045 passed before death, 0 failed), with this group SIGKILLed.
  The four native read/print tests and the print process mutation controls pass.
  Running the read-loop mutation controls alone with
  `scripts/test -p heather-elab --test read_loop_process slow_acceptance_read_loop_refusals`
  also ends INCOMPLETE by SIGKILL at the existing CPU rail. The baseline
  whole-group run with old `conv.rs` reproduces the same rail failure.
  All caps and skip lists remain unchanged; the prefix-sharing experiment
  was reverted. This issue remains open and owns the incomplete suite result.

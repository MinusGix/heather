---
title: Restore resource margin for narrow certificate tests
status: closed
labels: [tests,function-ir]
created: 2026-09-20
updated: 2026-09-20
---

The ordinary full-suite run for byte-load composition reports 299.2 CPU seconds
for function_ir_narrow_certificates.rs against the unchanged 300-second rail.
The preceding typed-publication run reported 296.6 CPU seconds. This is test-run
resource evidence, not an A/B performance measurement or a claimed regression.

Separate the complete search_body certificate check from primitive narrow-value
certificate/control checks (or share their checked prefixes without weakening
kernel validation), so normal scheduling variation cannot kill the target.
Keep every existing positive and negative check, preserve whole-library rebuilds
in the full lane, and do not raise limits or hide failures behind ignored tests.

Related: [[certgen-harness-cost]] and [[scripts-test-killed-binary-reads-green]].
The feature being exercised is owned by [[native-bounded-loop-certificates]].

## Log

- 2026-09-20: The byte-load composition full suite confirmed the resource failure: the narrow
  certificate binary was killed with SIGKILL and no result line at the 300-second
  rail (299.2 CPU seconds reported). All completed targets had zero assertion
  failures; the runner correctly reported INCOMPLETE rather than success.

  Moved the existing complete search_body physical certificate test unchanged to
  function_ir_search_certificates.rs. Primitive narrow proofs and their controls
  remain in function_ir_narrow_certificates.rs. Every assertion and kernel check is
  retained; only the process boundary changes. No limits or ignored tests changed.
  Plain full validation will be rerun.
- 2026-09-20: Final plain scripts/test passed 2863 tests, 0 failed, 5 ignored. The split
  primitive and complete-body targets both complete under unchanged limits.
  Every original assertion is retained; no tests were ignored. This resolves
  the combined process's CPU-limit failure.

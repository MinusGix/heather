---
title: Restore native certificate acceptance within the existing CPU budget
status: closed
labels: [x86,kernel,elaboration,performance,testing]
created: 2026-09-08
updated: 2026-09-08
---

Merging `df25c3f` into the reusable-callee baseline `cb877f2` exposed CPU-limit
failures in the two-placement native executable test and the CLI unit-test
binary. The initial full run reported 2484 passes, one failure, and an
incomplete suite: the executable's checker child was killed around 303 seconds,
and the CLI unit-test binary had no final result line after SIGKILL.
The host was busy; these runs establish a resource failure, not an attributed
performance regression or a controlled speed comparison.

The extended kernel checks passed (333 tests). A benchmark run overlapping
other work flagged regressions; a repeat with this agent's tests finished
passed all 106 comparisons. Neither establishes that the host was quiet.

## Acceptance

- Attribute prefix loading/rechecking separately from generated-certificate
  elaboration and kernel checking. For CLI unit tests distinguish one expensive
  proof from the aggregate budget of multiple tests in one process.
- Attribute the responsible conversion/reduction work. Any claim of a kernel
  regression or speedup requires comparison against the pre-merge parent under
  the recorded benchmark protocol with controlled host load.
- Restore the existing two-placement executable and CLI controls under unchanged
  memory/fuel/CPU limits; retain fetch, frame, source-result, and refusal evidence.
- Do not substitute smaller example inputs or weaken the proof boundary to pass.
- Record a complete final `scripts/test` result, including any unrelated failures.

## What it assumes from elsewhere

- [[generated-proof-cost-diagnostics]] owns reusable cost instrumentation.
- [[state-projection-conversion-cost]] owns the minimized state-history family.
- [[bitvec-width-bounded-defaults]] owns the choice of default arithmetic APIs.
- [[kernel-native-depth-budget]] owns graceful refusal before native stack
  overflow; the observed failures here are a distinct CPU-budget problem.

## Log

- 2026-09-08: Replaced producer displacement chains with the checked ripple
  add/sub bridges. Focused call controls pass, including high-bit and wrapping
  operands, but the focused executable still hits the CPU limit. The shorter
  producer proof alone does not resolve this issue. Diagnostic instrumentation
  is confined to a temporary build outside the repository.

- 2026-09-08: A temporary declaration-timing build, with kernel-rechecked stale
  library images for diagnosis only, completed 1614 declarations (about 275s
  accumulated wall time) before the CPU cap. Byte-fetch declarations accounted
  for about 125s of that partial trace; the summary definition itself was about
  4.3s. It stopped during `caller_native_read_literal_28_5`. These are noisy,
  instrumented attribution data, not benchmark results. The file is a header/code
  concatenation and each raw lookup traverses the header. A checked prefix-skip
  helper using `list::nth_append_r` is being tested as a bounded improvement;
  its effect on the final acceptance budget is not yet established.

- 2026-09-08: The prefix-skip helper passed neutral-library and concrete fetch
  controls, including a corrupted byte. The complete two-placement executable
  then passed under unchanged limits (223.75s reported), still exiting 3 with
  the same source/fetch/frame claims. Final whole-suite acceptance, especially
  the aggregate CLI unit-test target, is pending. This is an acceptance result,
  not a controlled performance comparison on the busy host.

- 2026-09-08: Final plain `scripts/test` passed: **2494 passed, 0 failed,
  5 ignored**, including the two-call executable and complete CLI unit-test
  target, under unchanged limits. The checked ripple bridges and file-prefix
  lookup helper are retained. Extended kernel checks passed 333 tests; the
  repeat benchmark gate passed all 106 comparisons. The concrete acceptance
  failure is resolved. No controlled speedup or kernel-regression claim is made;
  general conversion attribution remains with [[state-projection-conversion-cost]].

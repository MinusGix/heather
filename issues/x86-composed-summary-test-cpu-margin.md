---
title: Restore per-process headroom for composed-summary tests
status: closed
labels: [compiler,x86,tests]
created: 2026-09-19
updated: 2026-09-20
---

## Scope

Restore comfortable CPU headroom for the CLI unit-test binary as generic
composed-summary acceptance and mutation coverage grows.

The multiple-save-slot extension initially crossed the existing 300-second CPU
rail. Sharing each fixture's checked leaf prefix and reusing checked state facts
for the postcondition mutation reduced the full-run CLI target to 277.0 CPU-s
(92%). The final full suite passed 2832 tests with zero failures and five ignored.
The two-slot native integration target used 207.5 CPU-s; the one-slot two-call
target used 192.2 CPU-s. These are test-process measurements, not proof fuel.

## Acceptance

- Attribute remaining repeated checking and reuse checked prefixes where safe,
  or move independent acceptance families into separate bounded test binaries.
- Retain neutral-state acceptance and every load-bearing mutation control.
- Keep the kernel, proof fuel, memory limits, and per-process CPU rail unchanged.
- Verify a plain full suite and record per-target CPU headroom.

## What it assumes from elsewhere

- [[x86-composed-caller-multi-slot-spills]] owns the completed multi-slot feature.
- [[native-summary-test-cpu-margin]] records the previous worker-contention fix.
- [[generated-proof-cost-diagnostics]] owns general proof-cost attribution.

## Log

- 2026-09-19: The buffer-cursor milestone adds its acceptance and refusal coverage in a separate bounded integration target (33.0 CPU-s). The existing CLI unit target remains near its limit: 291.1 CPU-s in the first full run, which passed all functional targets and failed only a new model's whitespace check. Further unit-target headroom remains open; no resource limits were changed.
- 2026-09-19: Final plain suite for [[x86-buffer-cursor-recognizer]] passed 2833 tests, 0 failed, 5 ignored. The unchanged CLI unit-test family reached 295.5 CPU-s (99% of 300) in this run. The new parser primitive's tests remain in their own native_buffer_cursor binary. This headroom issue should be addressed before adding further expensive checks to the existing CLI unit target.
- 2026-09-20: The independent sharing/register/stack-save proof fixtures now run in individual child processes of the same test executable, with the runner's existing memory and CPU rails inherited unchanged. The parent performs no checking for that family; each child selects exactly one fixture. All mutation controls remain. This restores per-process budget separation, not an aggregate CPU-cost reduction. The targeted family passed; final full-suite verification is pending.
- 2026-09-20: The first full run exposed a re-exec race: an independent Cargo build replaced the running test binary, so current_exe returned a deleted path and the next child could not start. On Linux the harness now re-execs /proc/self/exe, preserving the running inode even after unlink/replacement; each child's output must also confirm exactly one passing test. The 163.4 CPU-s figure from that failed run is not a completed-family headroom measurement and must not be treated as final validation.
- 2026-09-20: Final plain suite passed 2834 tests, 0 failed, 5 ignored. All four isolated proof fixtures and their mutation controls completed with the unchanged 6 GiB/300-second per-process limits. The runner reports 317.4 CPU-s for the CLI target including its descendant processes; that aggregate is not the parent's consumption and no aggregate CPU reduction is claimed. [[test-cpu-rail-child-accounting]] tracks the misleading per-process percentage attached to aggregate timing. This issue is resolved through the independent-process acceptance option, retaining every control.

---
title: Make adaptive parallel test jobs robust to simultaneous heavy semantic targets
status: open
labels: [testing,tooling,performance,parallelism,memory]
created: 2026-09-02
updated: 2026-09-02
---

The full FunctionIR block-argument verification selected five concurrent
children from its startup `MemAvailable` calculation.  It began the five
largest semantic targets together.  `function_ir_x86_alu` completed at
289.32s, then `function_ir_x86_control_flow` and `omega_div_mod` were both
reported as SIGKILL at 319.17s/319.69s, within half a second of one another.
The suite correctly reported `INCOMPLETE`: 2,291 passed before death and zero
test failures.

The FunctionIR control-flow target immediately passed alone under the same
4-GiB/300-CPU-second rails in 152.42s.  `omega_div_mod` is independently known
to sit close to its rail, but two simultaneous SIGKILLs strongly suggest that
startup-only aggregate memory sizing or heavy-target co-scheduling also needs
investigation.  Do not raise per-process rails or weaken killed-target
detection.

## Acceptance

- Distinguish per-process CPU-limit death from cgroup/global OOM in runner
  diagnostics when the host exposes enough evidence.
- Sample available/cgroup memory while scheduling, not only once at startup,
  or reserve enough dynamic headroom that unrelated host growth cannot erase
  the nominal 2-GiB reserve.
- Consider a weighted/exclusive class for the few semantic targets whose
  measured peak RSS makes address-space caps a poor aggregate-memory proxy.
- Reproduce a complete full suite at the adaptive default without reducing
  correctness coverage.

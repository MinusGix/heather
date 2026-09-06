---
title: Make adaptive parallel test jobs robust to simultaneous heavy semantic targets
status: open
labels: [testing,tooling,performance,parallelism,memory]
created: 2026-09-02
updated: 2026-09-05
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

## Log

- 2026-09-04: 2026-09-04 full run (this branch, cold images under Exact after a format change): function_ir_x86_control_flow was SIGKILLed again at the rail under three-way contention while function_ir_x86_alu passed at 235 s (289 s on 2026-09-02); the reported 319 s for control_flow on 2026-09-02 was a kill too, so the target has been dying in the parallel full lane since the shard split. Separately, function_ir_x86_source failed deterministically: eb1f01a (2026-09-03) inserted x86_64_control_flow into the fixture MODULES list, and two hard-coded MODULES[..15] slices (the stale-source control and the shared-DAG source test) then stopped before function_ir, so the probe's import failed. Fixed to MODULES.len() - 1 like every sibling site.
- 2026-09-05: 2026-09-05 full run ([[omega-per-goal-elaboration-cost]] round, 7 jobs): function_ir_x86_alu SIGKILLed at the rail (305 s reported) after passing at 241 s in the previous run of the same code. Serial it is 117 s on that branch (268 s at its base), so the kill is contention at ~2.5x, consistent with the entries above.
- 2026-09-05: Datum (2026-09-05, decreases-unfolding round): on a host with ~23 GiB used by other sessions and swap exhausted, a CLEAN-tree full scripts/test came back INCOMPLETE with four targets SIGKILLed (function_ir_x86_alu/_conditionals/_control_flow, termination_measures), each passing standalone under the runner's exact ulimits (~100 s, 1.5-2.2 GiB). The round adds decreases_unfolding.rs (8 tests, ~100 s, ~1.5 GiB; same full-std prefix as termination_measures) — one more target of the shape that dies first under load. Lever unchanged: [[integration-test-prefix-reelaboration]] for the prefix cost.

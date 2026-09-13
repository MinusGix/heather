---
title: call_run_checked is one library theorem worth a third of the reused_callee workload's kernel gate
status: open
labels: [stdlib,x86,kernel,performance,proofs]
created: 2026-09-13
updated: 2026-09-13
---

From the 2026-09-13 checkpoint table (release, value-metrics, W=1, `build-x86 examples/x86-native/reused_callee.hthr caller --callee leaf`, cold, one furnace E5 box): whole workload 4,997 items, item total 92.4 s, kernel gate 64.1 s, 46.6 M steps, 361,641 misses. The top row is a single item:

| item | total s | kernel s | misses | steps | shortcut hits |
| --- | --- | --- | --- | --- | --- |
| `call_run_checked` (lib/std/arch/x86_64/call_summary.hthr) | 28.7 | 23.4 | 8,100 | 15.6 M | 1.09 M |
| `caller_native_byte` (36 items) | 4.8 | 4.0 | 34,515 | 2.6 M | |
| `call_trace_append` | 3.8 | 2.9 | 850 | 1.8 M | |

One theorem is 37 % of the gate and a third of all evaluator steps; the next family is six times smaller. It sat unremarked in the round-4 table (docs/bitvector-literal-entry-design.md §10.6: 23.68 → 23.29 s across that round, i.e. not bitvector-shaped). It is library time — paid per cold library build and replayed from the image otherwise — so it does not tax a compiled program the way the certificate families do, but 15.6 M steps for a structural induction over `List<CallInstruction>` with an `Exists`/`∧` premise chain is a pathology: the theorem is a `match` with one recursive call and a handful of projections, `j`, `trans`, `cong_fn`. Attribute before touching it (`--timings` plus the conv-miss sampler on `heather check lib/std/arch/x86_64/call_summary.hthr`): the likely shapes are the premise record's projections `premises.proof.right.right.right` computed through per-instantiation references ([[per-instantiation-projection-boundaries]]), or `call_next`/`call_run` unfolding under the motive.

Trigger: any round that measures cold library time, or the next x86 spelling round. Related: [[x86-64-machine-model]], [[x86-calls-stack-frames]], [[function-ir-x86-proof-scaling]].

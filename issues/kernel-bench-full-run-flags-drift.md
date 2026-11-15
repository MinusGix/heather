---
title: The kernel bench's full --check flags a different 1.25-1.5x set every run while every filtered re-run is ok
status: closed
labels: [kernel,tooling,performance]
created: 2026-08-17
updated: 2026-09-11
---

Observed 2026-08-17 as the end-of-round gate of the motive-synthesis round (docs/elaborator/goal-motive-synthesis-design.md), and recorded because the round could not tell "my change regressed something" from "this harness's time half does not repeat" without four runs.

Four consecutive full `scripts/bench --check` runs on the same binary and the same baseline, minutes apart, on an otherwise idle desktop:

- run 1: 6 flags — level/equiv-shared:16, subst/shift-local:263, nat/step-into-closed-body:256/512/1024, check/generated-terms:200
- run 2: 3 flags — nat/step-into-closed-body:256/512 and one more
- run 3: 6 flags — level/equiv-shared:4/8/16, code/check-identity-recursor:33, code/whnf-identity-recursor:3, check/generated-terms:200
- run 4: 1 flag — conv/perturbed-pairs:100

Nine distinct fixtures across four runs, no fixture flagged in all four, every magnitude in the 1.25-1.5x band, i.e. just over the 1.25x gate. Meanwhile **every filtered re-run of a flagged family is green**: `--check --filter subst` ok (12 comparisons), `--check --filter check` ok twice (21 comparisons), with check/generated-terms:200 at 4.13-4.15 ms filtered against 4.72-4.81 ms in a full run and a 3.77 ms baseline. And in all four runs **every scaling exponent was inside its expected band** — the headline number docs/infrastructure/benchmarking.md says to read.

This is the same *signature* as [[frontend-bench-heavy-contaminates-cheap-cases]] on the other harness: a family reads 1.3x slower when something big has run before it in the same process, the gate sits below the contamination, and the flags are therefore unactionable. Whether the mechanism is the same (allocator/reclaim state after a large workload) is not established here; what is established is that the kernel suite's time half does not repeat within its own threshold on a full run, and that the four candidate fixes that issue lists apply to this harness too — the harness is a sibling, not a shared crate, so a fix has to be made twice or the two have to be unified.

Cost to a round: this round ran the full check four times plus three filtered runs to reach "no evidence of a regression", which is the wrong ratio for a gate that is supposed to be one line.

Not filed as a defect in this round's change: the change touches the substitution traversal (one default-`None` `Mapper::pre_tm` hook), and subst/apply-local and subst/shift-local are green when measured alone.

## What it assumes from elsewhere

- **[[frontend-bench-heavy-contaminates-cheap-cases]]** owns the same finding on the frontend harness. Assumed here: nothing but its existence — the mechanism it suspects is a hypothesis for this one, not a shared conclusion.
- **[[kernel-benchmarks]]** owns the suite and its thresholds. Assumed here: only that the time half gates at 1.25x.

## Log

- 2026-08-17: Fifth run, coordinator, at merge verification (2026-08-17): the merged tree's full scripts/bench --check on a quiet machine was fully green — ok 106 comparisons, zero flags. Consistent with the intermittent signature (four runs: 6/3/6/1 flags; fifth: 0) rather than with any fixture being reliably slow.
- 2026-08-17: Sixth full run, end-of-round gate of the argument-type-reduction round ([[motive-application-hides-hypothesis-type]]): ok, 106 comparisons, zero flags, on a machine running nothing else. Second consecutive clean full run (fifth was the coordinator's merge verification). Running tally of flags per full run on essentially the same tree: 6 / 3 / 6 / 1 / 0 / 0 — still consistent with the intermittent signature and with no fixture being reliably slow. No disambiguation run was needed by this round, so it cost the one line a gate is supposed to cost.
- 2026-08-17: Seventh run (coordinator, merged-tree verification of the argument-type-reduction round, 2026-08-17): fully green, ok 106, zero flags. Tally 6/3/6/1/0/0/0.
- 2026-08-18: Eighth and ninth runs, end-of-round gate of the congruence-in-inference-position round (elaborator-only change; crates/kernel untouched, verified with git diff). Run 8 flagged NINE, all of nat/add-normalize and nat/mul-normalize, every size, uniformly 1.47-1.67x -- and it was run while a SIBLING agent's scripts/test --fast was saturating the machine from another worktree. Run 9, same binary and baseline, on a quiet machine: ok, 106 comparisons, zero flags. Tally 6/3/6/1/0/0/0/9/0. New datum for the four candidate fixes: this is the first run where the flagged set was a coherent FAMILY at a uniform ratio rather than a scattered handful just over 1.25x, and it had an identifiable external cause. Worth distinguishing in whatever fix lands -- a whole family at 1.5x is machine load and could be refused outright (or the harness could decline to compare times when load is high), whereas the scattered 1.25-1.5x singletons of runs 1-4 are the harder, in-process contamination signature.
- 2026-09-11: Merged into [[perf-tracking-consistent-environment]] 2026-09-11: the tally here is the evidence its 2026-08-18 decision rests on; nothing is separately actionable. Closing.

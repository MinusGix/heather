---
title: Consistent perf measurement: a place where a regression is a signal, not noise
status: open
labels: [performance,tooling,testing,meta]
created: 2026-08-11
updated: 2026-09-17
---

Filed from the 2026-08-11 iteration-time review. Two observations met:

1. Ad-hoc perf measurement keeps leaking into rounds that should not care.
   The bare-symbol round timed `heather check` by hand (a failed
   `/usr/bin/time` attempt, then a date-based loop) to prove a respelling
   was free — which CLAUDE.md now says plainly: an ordinary round does not
   measure. But the instinct came from somewhere real: nothing else would
   have noticed a regression.
2. The user's machine cannot be the baseline: "I'm always doing random
   stuff" — wall-clock numbers taken beside a browser build are noise, and
   the §12.7-style bands recorded in design docs go stale the moment the
   hardware or the load changes.

What exists: `scripts/bench --check` gates the kernel against
`crates/kernel/benches/baseline.tsv`, and its headline is the **scaling
exponent**, which is the one number that survives a machine change
(docs/benchmarking.md). Nothing gates the elaborator or the whole-library
checks; their §12.7-style bands live in prose.

The question this issue owns: what is the *program or environment* whose
numbers are consistent enough that a notable regression is a signal?
Directions to weigh, not decided:

- **Count instructions, not seconds.** `perf stat` retired-instruction
  counts (or cachegrind) are nearly load-immune and machine-comparable to
  first order; a `scripts/bench`-style gate over "instructions to check
  lib/std + ir_v1" would run fine on a busy machine. The harness stays
  first-party (dependency-policy: the kernel keeps zero deps; a script
  invoking perf is a script, not a dependency).
- **Extend the exponent discipline** from the kernel benches to elaborator
  workloads: exponents need less quiet than absolute times, and
  docs/benchmarking.md already explains why they are the headline.
- **GitHub CI** — unknown runner consistency (shared, throttled, changes
  under you); probably fine for exponents/instruction counts, useless for
  wall-clock bands. Also: is this repo even hosted where CI can see it?
- **A dedicated cadence** (nightly cron on an idle machine) if one exists.

Related: the one-deliberate-perf-round-per-session discipline is *when*
perf work happens; this is *where its numbers come from*.
[[bounds-metadata-taxes-one-shot-checking]], [[certgen-harness-cost]] and
[[synthesis-direction-cost-asymmetry]] all recorded "levers if it grows" —
each assumes something will notice growth, which is this issue.

## Log

- 2026-08-12: Policy sharpened with the user (2026-08-12), triggered by CLAUDE.md's fast-lane '~30s' having gone stale unnoticed: CONCRETE PERF NUMBERS DO NOT BELONG IN DOC FILES OR CLAUDE.md, except abstractly. Docs may carry shape claims -- scaling exponents, what dominates, which lever exists -- because those survive hardware and load changes (docs/benchmarking.md's exponent headline is this policy already applied); wall-clock numbers belong in dated issue-log entries, which are diary by construction and expected to age, and in baseline.tsv behind scripts/bench --check. CLAUDE.md's fast-lane line re-edited accordingly (abstract statement + pointer to certgen-harness-cost for current numbers). This strengthens the instruction-count direction above: retired-instruction gates are the version of 'a number a doc could almost trust' -- load-immune to first order and runnable on the user's busy machine. Second user position recorded the same day, adjacent and load-bearing: perf surprises are usually pathologies or missing smarts, not laws -- do not distort designs around them; file the mechanism question instead (first instance: [[wf-field-conversion-cost]], the 163x from round A).
- 2026-08-16: Datum for the 'is a regression a signal?' question, 2026-08-16: scripts/bench --check FAILED once and passed on an immediate re-run of the SAME tree (18 comparisons within thresholds), on a diff that touches only crates/syntax's parser — no kernel path at all, so a real regression was not available to it. Which comparison failed is unknown: the run's output was truncated to its last lines and the detail was lost, which is its own small lesson for anyone running the gate from a script.

What this says for the directions above: the exponent discipline is doing the load-immunity work it was chosen for, but the gate still has a false-positive mode on a busy machine, and a gate that cries wolf once a session gets re-run rather than believed — which is the failure this issue exists to prevent. It is a second, independent argument for the retired-instruction direction (a false positive costs a full re-run, ~4 min, and teaches the wrong reflex), and an argument that whatever the gate becomes should print enough on failure to name the comparison without a re-run. Not investigated further and not filed separately: one occurrence, no mechanism, and the round it interrupted had no perf stake.
- 2026-08-18: User positions recorded (2026-08-18), and two of the directions are decided. (1) Trust policy for wall-clock on the desktop: believed directionally ('making it go down is gooder') and at order-of-magnitude changes only -- the 1.25x time gate is below this machine's noise floor (the 6/3/6/1/0/0/0/9/0 flag tally on [[kernel-bench-full-run-flags-drift]] is the evidence), and the user expects much of that tally is variable machine load. (2) The instruction-count gate is the chosen direction for the per-round gate; verified this machine counts unprivileged (perf stat -e instructions:u works at perf_event_paranoid=2). Its round is not yet scheduled. (3) GitHub CI is rejected for perf (shared runners are noisier than the desktop; the things they could do well, instruction counts do locally for free). (4) The dedicated-cadence direction is APPROVED and being set up 2026-08-18: the user's low-perf server (ssh mc; 2 cores, 3.8 GiB, Ubuntu) gets an explicit-trigger bench run plus a ~3am nightly, stopping the game servers it hosts for the run -- only when no live player connections (the user's friend may be on), detected before stopping anything. Wall-clock numbers from it are a quiet-hardware TREND diary, not a gate; its baseline coexists with the desktop's via the cpu+profile+rustc keying.
- 2026-08-18: Second purpose for the server cadence, user position (2026-08-18): the slow box is also a LENS, not only a quiet diary -- shoddy hardware surfaces decisions a fast machine chunks through, so the reading protocol is column-wise ratios against the desktop, where the uniform ~4-5x constant is the null hypothesis and a family that departs from it (8x where its siblings sit at 5x) is the signal worth an accumulator issue. First entry's whisper: kernel share of ir_v1 rises ~64% -> ~82% on the slow box, forded families 88-95% kernel there. Adjacent user position, recorded so perf findings do not argue against it: the kernel stays deliberately un-fancy until Heather-in-Heather can PROVE the properties that make fanciness safe; verified cleverness then lands in the development fast mode first. A perf surprise is a pathology to file, never a case for kernel cleverness ahead of its proofs.
- 2026-09-11: Datum (2026-09-11, arena-pooling design pass): scripts/bench --check on a furnace box (EPYC 9J14) against the committed Ryzen 5700X baseline degrades to shape-only (88 of 106 comparisons skipped for env mismatch) and exits 3, which scripts/bench reports as failure. Working furnace protocol: --save at the before commit in the same job, apply, --check, then git checkout the baseline. Never commit the furnace baseline. Owner question for this issue: a per-environment baseline file or an env-keyed section, so --check can gate time where the rounds actually run.
- 2026-09-11: Merged in [[kernel-bench-full-run-flags-drift]] and [[frontend-bench-heavy-contaminates-cheap-cases]] (2026-09-11). Both are the same finding on sibling harnesses: the 1.25x wall-clock gate sits below the machine's noise floor (nine-run tally 6/3/6/1/0/0/0/9/0; heavy corpus cases contaminate later families 1.3-1.5x). This issue's 2026-08-18 position already acted on that evidence (instruction-count gate chosen, not yet scheduled). The interim protocols stay: filtered re-runs for the kernel bench, --no-heavy for the frontend bench. Note also the 2026-09-11 cross-box datum: --check on furnace against the desktop baseline is shape-only, 88 of 106 comparisons skipped.
- 2026-09-17: 2026-09-17: the dated environment-keyed diary this issue's 08-12 policy asked for now has a home and a reader: [[perf-dashboard]] (scripts/perf snapshot/report/serve, perf/snapshots/). The quiet-server cadence is down with its server; the diary takes the desktop and the furnace as its two environments.

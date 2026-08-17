---
title: A host rename silently turns off half of bench-frontend --check, and the only signal is one line of prose
status: open
labels: [frontend,tooling]
created: 2026-08-17
updated: 2026-08-17
---

## Log

- 2026-08-17: FOUND 2026-08-17 (managed tooling round), while re-recording the frontend baseline. `crates/elab/benches/baseline.tsv` recorded `env host minus-pc`; this machine answers `minus-desktop` to hostname. The harness compares `env` rows and, on a mismatch, sets `Thresholds::compare_times = false` -- correctly, since absolute times from another machine mean nothing -- and prints one line: "baseline is from another machine or profile (minus-pc / release) -- comparing scaling shape and latency budgets only, not times". Then it says "ok: 9 comparisons within thresholds" and exits 0.

So HALF THE GATE HAD BEEN OFF on this machine, and the visible symptom was a green gate with a suspiciously small comparison count -- 9, where a matching baseline gives 50 (--no-heavy) or ~57 (full). Two rounds read time regressions off this suite in early August (see [[frontend-benchmarks]]'s 2026-08-08 entry), so the host string matched then; whatever renamed the machine turned those comparisons off silently, and every --check since has been shape-only.

Three things would each have made this visible, cheapest first: print the comparison count next to what a full comparison WOULD have been ("9 comparisons -- 48 skipped: baseline host minus-pc, this host minus-desktop"); make the skipped half a distinct non-ok exit state (a gate that skips half its checks is not "ok"); or key comparability on cpu+profile+rustc rather than the hostname, which is the field with no bearing on how fast the machine is. This issue prefers the second plus the first: "ok" should mean "everything was checked".

The 2026-08-17 re-record (host minus-desktop) turned the time half back on, which is how [[frontend-bench-heavy-contaminates-cheap-cases]] became visible at all.

## What it assumes from elsewhere

- **[[frontend-benchmarks]]** owns the suite and its baseline. Assumed here:
  only that a baseline whose `env` rows disagree with the machine is compared
  for shape and not for time -- which is correct, and is not what this issue
  disputes.
- 2026-08-17: IT IS BOTH SUITES, not just the frontend one (same round, 2026-08-17, noticed while taking the round's closing verdicts). `scripts/bench --check` -- the kernel gate, the one CLAUDE.md tells every round to run -- prints "baseline is from another machine or profile (minus-pc / release) -- comparing scaling shape only, not times" and then "ok: 18 comparisons within thresholds", exit 0. So the kernel suite's absolute-time comparisons are off on this machine too, for the same reason, and its green has been a shape-only green for however long the host string has disagreed.

That doubles the case for the fix being in how the two harnesses REPORT a skipped half rather than in either baseline: "ok" should not be printable by a run that compared shape only. [[kernel-benchmarks]] owns the kernel suite; this issue owns the mechanism, which is shared by construction (the frontend harness is a sibling of the kernel's, docs/frontend-benchmarking.md's last section).

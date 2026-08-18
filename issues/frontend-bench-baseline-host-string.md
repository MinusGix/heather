---
title: A host rename silently turns off half of bench-frontend --check, and the only signal is one line of prose
status: closed
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
- 2026-08-17: 2026-08-17, coordinator, at merge: CONFIRMED for the kernel suite too, and it needs its own decision. `crates/kernel/benches/baseline.tsv` records `env host minus-pc` (commit 0674cac) and this machine answers `minus-desktop`, so `scripts/bench --check` is in exactly the state this issue describes — today's four green '18 comparisons within thresholds' verdicts (three round commits plus the merge) are SHAPE-ONLY, and every one of those commit messages should be read that way. The frontend baseline was re-recorded in this round because the round's subject was the frontend instrument; the kernel one deliberately was NOT, for two reasons: it is the gate CLAUDE.md points every round at, and re-recording a perf baseline is a decision to take deliberately rather than as a side effect of a tooling round on a different suite. What it needs is a decision between re-recording on this host and this issue's own preferred fix (key comparability on cpu+profile+rustc rather than hostname, which has no bearing on how fast the machine is) — the second would restore both suites at once and would have prevented this. Until then, no round should read a kernel TIME comparison off `--check`; its scaling-exponent verdict is unaffected and remains the headline number per CLAUDE.md.
- 2026-08-17: RESOLVED (bench-gate round, direct): both harnesses now key time comparability on cpu+profile+rustc and never consult the hostname; a run that skipped its time half prints 'shape-only: N comparisons -- M skipped' naming the mismatched env field with both values, and exits 3 instead of printing 'ok' and exiting 0 -- this issue's preferred fix (the second plus the first), plus the third for good measure. The kernel baseline was re-recorded on this host/toolchain (the deliberate decision the roadmap scheduled): drift accounting against the 0674cac (2026-07-31) baseline shows the expected improvements from the subst/kernel-defs rounds (wf/check-tree 0.39x, check/generated-terms 0.57-0.77x, nat/check-numeral ~0.58x) and one uniform constant-factor slowdown, level/equiv-rebuilt 1.33-1.43x with slopes unchanged, consistent with the accepted tax on bounds-metadata-taxes-one-shot-checking (logged there). Post-re-record: scripts/bench --check ok 106 comparisons (was 18 shape-only), scripts/bench-frontend --check --no-heavy ok 50 comparisons. The frontend quick-mode 1.25-1.38x flags seen mid-round did not reproduce on a quiet full run -- load noise, as --quick's own warning predicts.

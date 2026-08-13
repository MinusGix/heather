---
title: A ulimit-killed test binary reads as a green suite line with a smaller count
status: closed
labels: [testing,tooling,robustness]
created: 2026-08-12
updated: 2026-08-13
---

The one line scripts/test tells callers to read — `== suite: N passed, 0 failed, 0 ignored ==` — is computed by an awk sum over cargo's per-binary `test result:` lines. A binary killed mid-run contributes nothing to the sum, so the summary prints a SMALLER passed count with `0 failed`: a false green on the exact line CLAUDE.md instructs humans and agents to trust instead of re-running to grep. The script's *exit code* is nonzero (`set -o pipefail` catches cargo), but nobody reading the transcript's last line sees that, and the kill message (`(signal: 9, SIGKILL)`) scrolls away above ~60 targets' output.

Seen twice, both under the 300 s `ulimit -t`: [[scripts-test-fail-fast]]'s era (the shape [[certgen-harness-cost]]'s log calls "the same mis-read, seen again") and 2026-08-12's non-Nat round, where the with-fields first cut pushed `crates/elab/tests/certgen.rs` past the CPU cap and the summary reported a truncated 129-passed total. The failure mode is nastiest exactly when it fires: a *cost* regression (the thing the rails watch) masquerades as a *smaller test suite*, and an agent reading the suite line reports green.

Fix shape, either sufficient:
- have the summary see the exit status: run cargo to a temp file (or use `PIPESTATUS[0]` after the pipeline) and print `== suite: INCOMPLETE (a test binary died; see above) ==` instead of a count when cargo failed for any reason other than test failures — or unconditionally append `exit status` to the summary line;
- and/or have awk recognize cargo's `(signal:` / `process didn't exit successfully` lines and force a nonzero killed-count into the summary.

Cheap; no elaborator or kernel involvement. Trigger: next time anyone touches scripts/test, or the next time a rail is near a cap (which after the certgen split is most of the certgen family — see [[certgen-harness-cost]]).

## Log

- 2026-08-13: Fixed, both recorded shapes at once. The summary line moved from awk to bash: awk passes output through and writes passed/failed/ignored plus a kill/crash line count (cargo's `(signal: N` / `process didn't exit successfully` lines) to a temp file; bash reads the counts and `PIPESTATUS[0]` and prints `== suite: INCOMPLETE (a test binary died, exit S, K kill/crash lines; P passed before death, F failed) ==` whenever killed > 0 or cargo failed with zero test failures — a green-looking count can no longer print when a binary died. Cargo's run-step stderr now flows through the pipeline (2>&1): the kill message was stderr-only, so awk's counter never saw it until then (found in verification — the status branch fired, the line count read 0). Verified three ways: tail-logic harness on fake cargo output (green / ordinary failure / killed), a real green run (exit 0, normal line), and a real SIGKILL under a 5 s CPU-cap copy of the script (INCOMPLETE line, 1 kill line, exit 101). Ordinary test failures still print the normal counted line with cargo's exit code.

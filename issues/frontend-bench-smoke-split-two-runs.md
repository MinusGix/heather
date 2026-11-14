---
title: The frontend bench smoke compares a split's parse time with a different run's total, and fails under load
status: open
labels: [testing,performance]
area: infrastructure
created: 2026-11-14
updated: 2026-11-14
---

`every_family_builds_validates_and_runs_one_round`
(`crates/elab/tests/frontend_bench_smoke.rs`) asserts of every family's
split that `total_ns >= parse_ns + kernel_ns`. The two sides are not one
run's: `measure_phases` (`crates/elab/benches/frontend/fixtures/mod.rs`)
takes `total_ns` from the timed run and then parses the source again to
get `parse_ns`. Where the timed run does little (an image-first family
replays and does not elaborate), a second parse that is descheduled once
is longer than the whole run it is compared with.

Seen 2026-11-14 in a `scripts/test --pr` lane on a four-core cloud
container, on a diff that touches only `lib/`:

    family `scale/image-first-ordinary`: split exceeds the run it came from

The test passed alone straight after (`scripts/test -p heather-elab --test
frontend_bench_smoke`).

## Routes

1. Take the parse time inside the timed run for the families that parse,
   and report no parse phase for a family whose timed run does not parse.
2. Keep the second pass and compare with a margin, or drop the comparison
   for families whose total is below some floor. Simpler, and still a
   comparison of two runs.

Route 1 is the one that makes the assertion mean what it says.

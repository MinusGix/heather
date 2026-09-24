---
title: Shard the full lane's longest unit-test binary (heather-cli, ~58 s of a 64 s lane) by test
status: open
labels: [testing,performance]
created: 2026-09-24
updated: 2026-09-24
---

The full lane's single longest target is `heather-cli (crates/cli/src/main.rs)`: 20 unit tests, ~111 s summed, run by one libtest process at two threads, so ~58 s wall against the lane's 64 s (2026-09-24, desktop, warm verdicts). Five `native::calls::callable::tests::slow_acceptance_*` tests are 10–35 s each.

Lever: the runner already shards `family_*` binaries by module (docs/elab-test-families-design.md §D3). The same mechanism could shard a long non-family binary by test (listing, then one `--exact` shard per test or per group), chosen from the timings history. Expected: that target's wall → its longest test (~35 s); the lane's wall → near its throughput floor (summed shard wall / jobs ≈ 52 s). At most ~12 s of full-lane wall; nothing for the fast lane, which skips these tests.

Danger: per-test shards change that binary's per-process state (a test relying on another's warm cache in the same process would run cold); the rails are per shard, which is stricter, not looser.

Trigger: the full lane's wall matters more than it does today, or this target grows.

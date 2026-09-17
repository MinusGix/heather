---
title: Find out where a furnace round trip's 2-3 minutes go
status: open
labels: [tooling,infrastructure,performance,measurement]
created: 2026-09-16
updated: 2026-09-16
---

A `furnace run` whose remote command takes 30 seconds takes 2–3 minutes
end to end. Where the rest goes has never been measured — candidates, in no
order: the rsync of the project tree, an `ensure`/SSH handshake per invocation,
output buffering (known to arrive in coarse chunks), cargo's up-to-date check on
a warm target dir, and whatever the wrapper does before and after.

This matters more than it looks. It is the constant added to *every* probe, so
it sets the granularity of the whole inner loop: it is why a five-second
question gets batched into a three-minute round trip with four other questions,
and why a bug in one of those five questions costs the whole trip
([[check-single-item-measurement]] is the other half of the same problem, from
the other end).

First step is a breakdown, not a fix: time each phase of one trivial
`furnace run -- true` and one realistic run, and publish the split. A plausible
outcome is that most of it is one avoidable thing (a per-invocation handshake, a
sync that walks `target/`), in which case the fix is small; another plausible
outcome is that it is six things at 20 seconds each, which is worth knowing
before anyone optimizes one of them.

Related: [[furnace-concurrent-jobs]] (serialization multiplies this constant by
the number of questions), [[furnace-run-invocation-ergonomics]].

## Log

- 2026-09-16: Filed from a session where ~8 probes of ~30 s of compute each
  consumed most of the wall time.

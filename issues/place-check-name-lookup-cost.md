---
title: place_check: name lookups make the closed verdict quadratic in program length
status: open
labels: [ownership,library,performance]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

`lib/lang/ownership/place_check.hthr`'s `check` costs the kernel a quadratic in the program's length, and the quadratic is name lookup, not the checker's logic ([[ownership-checker-spike]], log of 2026-11-25): names and word counters are unary `Nat`s compared by `same`, a name's buffer is `nth` into the plan list, the holder table is a closure with one layer per write, and the views table is appended with `++ [v]` and measured with `len()`; each is linear per operation. A program with no views shows the same growth as one with many.

Fix, when the checker runs on real code rather than probes: binary names (or words) and a map keyed by them for the holders and the plan, and the views table indexed the same way, which leaves the one cost the checker owes: a write scans the live views of its own object.

Not wanted before the checker meets code longer than a few hundred operations; the probes stay well under a second.

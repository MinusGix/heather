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

## Log

- 2026-11-25: The second experiment's checker (`lib/lang/ownership/call_check.hthr`, [[ownership-checker-call-and-write-view]]) is linear where this one is quadratic. Measured on the same shape (alternating set and get of one object), fresh `--cache-dir`, steps from `--timings`, at 16, 32, 64, 128, 256 and 512 statements: this module's `check` costs 9.5k, 20.8k, 50k, 136k and 414k steps, and runs out of fuel at 512 (2.4M); `check_fn` costs 6.7k, 12.9k, 25.3k, 50.1k, 99.8k and 187.6k, each doubling about 1.95 times the last. With views that die, and with calls, it stays linear (that issue's log has the rows).

  What made the difference there: no plan and no holder closure, because a function has one object and its holder is a counter; names compared by `same` against literal numerals, which the kernel's runs cancel cheaply, so unary names were not the cost; the live views a list that deaths shrink. So the quadratic here is `nth` into the plan and the holder closure's layer per write, as this issue said, not `same`.

  Still open for this module, and for the checker's next increment, with several objects ([[ownership-checker-loans-and-joins]]): the holder table and the plan as a `NatMap` keyed by buffer. One more cost found there: a verdict stated against a signature table written out costs about 95 steps per signature to read the table, whatever the call; the table should be one named value (and a map, if a lookup by position, about 7 steps an entry, ever matters).

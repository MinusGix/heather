---
title: Writes owe no bound in the ownership checker; the bytes level needs one
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

From [[ownership-site-facts-into-the-checker]]. Every element read now owes its bound (`Inside`), but writes (`Set`, `Put`) owe none: in this fragment a store past the reference does nothing in the run and `update` past the list does nothing in the meaning, so agreement holds, and the source's `update` is total. The bytes level (§18.3) has no store past a block, so a write owes its bound there; the reads' bounds are owed already for the same reason. Not built: what the source states for a write (`xs[j] = v` under `j < xs.len()`, or a total `set`) and where that proof comes from.

## Done when

`Set` and `Put` owe a bound the source discharges, or the design records why a total write needs none at the bytes level.

## Log

- 2026-11-25: Not a further round on `call_check.hthr` (docs/language/ownership-design.md §20): the experiment module is not extended again. This is a requirement on the checker built once over the fixed interfaces (§20.6) and is closed by that build.

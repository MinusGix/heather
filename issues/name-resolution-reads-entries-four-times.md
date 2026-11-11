---
title: Name resolution reads a name's entries up to four times, 1.1 M askings on the showcase
status: open
labels: [performance,elab]
area: language
created: 2026-11-11
updated: 2026-11-11
---

Name resolution is the largest named cost left in the elaborator's own code on a cold check. Left open by [[name-lookup-record-cost]]; listed in [[performance-overview-2026-11-11]].

## Measured

Callgrind, width one, cold `heather check --cache docs/showcase/calc_parser.hthr`, after the record fix: `Elaborator::key_of_kinds` is asked 1,102,275 times and costs 3,016 M instructions inclusive, about 2,700 an asking. That is 6.3% of the run and 7.9% of what a real run executes (the profile pays 9,400 M of scalar SHA-256 that the box does with SHA-NI).

`names::resolve_bare_kinds` is 1,736 M of it. For one name it reads the name's entries through the layered tables up to four times, notes the name for the lookup record at each read, and looks the origin up again for an entry it already holds.

## Directions

- One pass over a name's entries per asking, carrying the origin with the entry.
- A "same name as the last note" test in front of the record's hash: the same name is noted several times in a row.
- A per-declaration memo of resolved keys, if the same spelling is resolved many times inside one declaration. This needs a count first: how many of the 1.1 M askings repeat a (scope, name, kinds) triple.

## Done when

`key_of_kinds` is under half its current instruction count on the showcase, with identical `--timings` counter columns.

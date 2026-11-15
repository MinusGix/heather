---
title: Recording which names a module looked up cost 5% of a cold cached check
status: closed
labels: [performance,elab,cache]
area: infrastructure
created: 2026-11-11
updated: 2026-11-11
---

While a module is elaborated under `--cache`, the session records the last `::` segment of every name the elaborator looks up (`names::note`, `QUERIED`): the early cutoff's account of what the elaboration could have observed of the world's names beyond what its source spells (`docs/infrastructure/module-interface-cutoff-design.md` §2). Every lookup in the name tables notes its name, and resolution asks the tables about one name several times, so the record is consulted far more often than it grows.

## What it cost

Callgrind, width one, a cold `heather check --cache docs/showcase/calc_parser.hthr`: 49,756 M instructions, of which 9,400 M are scalar SHA-256 that only the profiler pays (the box hashes with SHA-NI).

- 3,285,067 notes for 6,275 distinct names.
- Each note built a two-way string searcher to find the last `::` (`rsplit("::")`, 729 M), then walked a `BTreeSet<String>` comparing strings on the way down (30.97 M `memcmp` calls, 647 M), 2,934 M in all. That is 5.9% of the run and 7.3% of what a real run executes.
- It is invisible without `--cache`: nothing records, and a note is one thread-local read (118 M on the same file). Every earlier whole-run profile in this series was taken without `--cache`, which is why it was found last.

## The fix

`crates/elab/src/names.rs`:

- the record is a `NameSet<String>` (the name tables' word hasher), so "is it noted" is one hash and one probe; `take_name_lookups` sorts it once into the `BTreeSet` its caller keeps;
- `last_segment` is a byte scan for the last `::`, held to `rsplit("::").next()` by a unit test over the edge spellings, as `split_qual` is held to `split_once`.

The record's contents are the same set, so every image's world record is unchanged.

## Result

Same run: 49,756 M to 47,600 M instructions (−4.3%; −5.3% without the profiler's hash). `names::note` is 772 M, `Elaborator::key_of_kinds` 4,858 M to 3,016 M inclusive.

Seconds, `scripts/perf ab`, six interleaved cold samples at width one on a cloud box, #553's tip against this change: wall medians 13.81 s and 13.60 s (the tool reports −2.2%), inside the per-sample spread, so not a result by the tool's rule. The columns where the lookups happen move the same way and more: `decl_type` 1.12 s to 1.07 s (−4.8%), `decl_body` 2.70 s to 2.60 s (−3.6%), everything outside the gate 9.73 s to 9.51 s (−2.3%). All 45 counter columns are identical across both binaries.

## Left open

Name resolution itself is the next thing in this profile ([[name-resolution-reads-entries-four-times]]): `key_of_kinds` is asked 1,102,275 times on the showcase and costs about 2,700 instructions an asking (3,016 M, 6.3% of the run), most of it in `resolve_bare_kinds`, which reads the name's entries through the layered tables up to four times, notes the name at each, and looks the origin up again for an entry it already holds. One pass over the entries would do. It also notes the same name several times in a row, which a "same as the last note" test in front of the hash would answer.

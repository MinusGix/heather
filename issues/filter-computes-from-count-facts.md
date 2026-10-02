---
title: A counting Filter's stdout claim from per-count facts, counts named once
status: closed
labels: [native,stdlib,ergonomics]
created: 2026-10-02
updated: 2026-10-02
---

A counting program states that stdout is its spec (`Filter`'s `computes`,
lib/filter_program.hthr). For wc, that equation is pure plumbing:
`wc_prints` rewrites three `j`s under `three_fields_line` and then appeals to
`counting_output`. The author's real fact is per count: the fold's field `i`
is spec `i` (`count_wc_input`).

The written bundle also says the counts twice. The type lists them, as
`[λ s => s.lines, …]`, and the finish lists them again, as
`Fields(λ s => s.lines, …)`. The CLI reads neither: it restates the counts as
the state's leading Nat fields (crates/cli/src/native/read_filter.rs, `context`).

Wanted:
- A library lemma that builds `computes` for a counting step from per-count
  facts. For `Line` and `Fields`, the facts are the finish's counts equal to
  specs `spec_i`, and stdout is the finish's line of the `spec_i`.
- `Finish` reads the program's `counts` by position (`Line` = the first,
  `Fields` = the first three) rather than repeating them, so a program names
  its counts once.

Stdout stays the claim: per-count facts are how it is proved, not what is
claimed.

Related: [[native-programs-read-like-programs]], [[fold-count-lemmas]].

## Log

- 2026-10-02: Landed 2026-10-02: Finish { Quiet, Line, Fields } reads counts by position; line_computes / fields_computes build computes from per-count facts; wc_prints/count_wc_input gone. Suite 3156.

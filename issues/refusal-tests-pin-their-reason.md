---
title: Refusal tests name the reason they expect
status: open
labels: [testing,tooling]
area: infrastructure
created: 2026-10-24
updated: 2026-10-24
---

About 260 tests only assert that elaboration fails (`is_err()`,
`unwrap_err()`, a `refused(src)` helper that reads nothing), and about 100
more accept some source and refuse other source the same way
(`scripts/test-census --list bare_refusal`). Such a test passes whenever
elaboration fails for *any* reason. A renamed lemma, a missing import or a
parse error keeps it green while it tests nothing
(`docs/test-value-audit.md` §3.6).

`crates/elab/tests/linux_wp.rs`'s `assert_refused` already does the right
thing: the first error must be the kernel's or the checker's refusal, not an
unbound name or a parse. Only that one file uses it.

## Proposal

- `support::refused(src, Reason)` with `Reason::Kernel`,
  `Reason::Elab("fragment")`, `Reason::Resolution`, `Reason::Parse`,
  generalising `assert_refused`.
- `scripts/check-elab-test-families.mjs` (it already walks every elab test
  file) prints the bare refusals as a warning list, to begin with. Make it an
  error once the list is short.
- Fix refusals file by file as they are touched. A refusal of a false
  *mathematical* claim usually becomes a `¬` theorem instead
  ([[library-tests-as-theorems]]).

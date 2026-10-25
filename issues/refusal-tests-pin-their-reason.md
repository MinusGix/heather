---
title: Refusal tests name the reason they expect
status: open
labels: [testing,tooling]
area: infrastructure
created: 2026-10-24
updated: 2026-10-25
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

## Log

- 2026-10-24: The helper exists: `support::assert_refused` with `Refusal::{Kernel, Mismatch, Says}` (crates/elab/tests/support). The float refusals use it. The rest migrate as their files are touched; `scripts/test-census --list bare_refusal` is the list. The lint in check-elab-test-families.mjs is not done.
- 2026-10-24: The census counts a test whose body or helper names a `Refusal::` as refusal-with-reason. The number, algebra and relation files now use `support::assert_refused` throughout ([[library-tests-as-theorems]]).
- 2026-10-25: Round 3 of the library migration gave every remaining library-family refusal a reason, `lib_setoid_mergeable.rs`'s eighteen included. One control was passing for an incidental reason: `bitvec`'s value-bound refusal wrote an unqualified `toNat`, so `<` had no meaning at its carrier. A `decide` refusal at a string goal spells the literal's kernel encoding ([[decide-refusal-spells-string-literal-encoding]]).

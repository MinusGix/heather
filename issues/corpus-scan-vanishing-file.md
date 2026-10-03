---
title: every_gt_is_accounted_for races a test that deletes .hthr files in the tree
status: closed
labels: [tests,flaky]
created: 2026-09-30
updated: 2026-09-30
---

`crates/syntax/tests/generic_delimiter_roles.rs`'s `every_gt_is_accounted_for`
walks every `.hthr` under `lib/`, `examples/` and `crates/`, then reads each
with `std::fs::read_to_string(path).unwrap()` (around line 53). During a full
`scripts/test` run on 2026-09-30 it panicked with `Os { code: 2, kind:
NotFound }`: a file the walk listed was gone before it was read. Run alone
(`scripts/test -p heather-syntax --test generic_delimiter_roles`) it passes.

Some other test, running at the same time, writes and deletes transient
`.hthr` files inside the scanned trees. `crates/cli/tests/check.rs` writes
edited copies (`fs::write` of `.hthr` paths), so it is the first suspect.

Fix: have the writing tests use a temp dir outside `lib/`, `examples/` and
`crates/`. If an in-tree file is intended, make the scan skip a file that is
`NotFound` when read instead of unwrapping.

## Log
- 2026-09-30: Fixed. The writer was `check.rs`'s
  `an_edited_module_replays_its_unchanged_declarations_from_the_previous_image`,
  which wrote and deleted `crates/cli/tests/fixtures/slice_edit.hthr`. Its
  edited copy now lives in a temp directory and is checked by absolute path.
  The other in-tree writers (`UPDATE_FUNCTION_IR_*` blessing,
  `HEATHER_FUNCTION_IR_X86_DUMP`, `target/` refusal dumps) are env-gated or
  outside the scanned trees. The scan stays strict: a file vanishing under it
  is a racing test worth hearing about.

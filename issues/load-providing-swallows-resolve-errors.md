---
title: loader::load_providing drops any resolve error for a bundled name
status: closed
labels: [cli, loader]
code: crates/cli/src/loader.rs @ 357c0afa
created: 2026-09-29
updated: 2026-09-29
---

`load_providing` leaves an import of a bundled module name to the native
builder when resolving it fails. It treats every failure that way, not only
"no such file": a name found in two search directories (an ambiguity the
loader otherwise refuses) is silently skipped, and the bundled copy is used.

Found adding the fallback for `examples/x86-native/wc.hthr`'s `import
bitvec_omega` (docs/native-wc-design.md §6.1). Fix: make `resolve` report
not-found apart from ambiguity, and fall back only on not-found.
Related: [[bundled-module-names-outside-build]].

## Log

- 2026-09-29: Fixed: `resolve` returns `Unresolved::Missing` apart from `Refused` (two hits in
  one tier, or a directory below the search path that can't be read), and
  `load_providing` leaves only a missing name to the caller. Test:
  `a_provided_name_covers_a_missing_module_but_not_an_ambiguous_one`
  (crates/cli/tests/check.rs), which fails on the old walk. With the modules
  findable as files ([[bundled-module-names-outside-build]]), a repository
  build now loads `bitvec_omega` from the file and compares it with the bundled
  copy; the fallback remains for a `heather` run with no `lib/` beside it.

---
title: loader::load_providing drops any resolve error for a bundled name
status: open
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

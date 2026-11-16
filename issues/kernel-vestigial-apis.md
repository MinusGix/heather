---
title: Remove Level::join's alias and the test-only bit_run_cons
status: open
labels: [kernel,code-health]
area: kernel
created: 2026-11-16
updated: 2026-11-16
---

Two kernel APIs whose comments explain why they still exist instead of
removing them:

- `Level::join` (`crates/kernel/src/level.rs:342`) is `Level::max` under
  another name, "from when `max` preserved a spelling and this one shrank
  it". Levels are canonical now, so the two are one function with 103 call
  sites of the alias across 25 files. Fix: rename the call sites to
  `Level::max` (or the other way) and delete the alias.
- `Val::bit_run_cons` (`crates/kernel/src/value.rs:2189`) is public but only
  called from the tests in `eval/bits.rs`. Fix: move it into that test module,
  or make it `#[cfg(test)]`.

Found by [[kernel-comment-audit]].

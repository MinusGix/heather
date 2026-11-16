---
title: Pass the β helpers a scope shape instead of a filler Γ
status: open
labels: [kernel,code-health]
area: kernel
created: 2026-11-16
updated: 2026-11-16
---

The shared β helpers take a `&LocalCtx` but read only its length and base
(`reduce.rs` module doc). So every caller that has no real syntactic Γ
builds one out of placeholder entries, each typed `Nat` at level 0, and a
comment beside it says this is fine because nothing reads an entry:

- `crates/kernel/src/conv/dom/values.rs:579` (`FILLER`, pushed at :1081 and :1869)
- `crates/kernel/src/eval.rs:395` (`Eval::scope`)
- `crates/kernel/src/conv.rs:850` and `:994` (`push_entry`'s filler)
- `crates/kernel/src/term.rs:1808` (`CtxEntries::repeat`, which exists for these)

The comments are the only thing keeping it true. If a helper ever reads an
entry's type (a lookup, a `ty_wf`, a debug print that is then trusted),
it gets `Nat` and answers silently wrong, not loudly.

## Fix

Give the helpers the shape they actually read: a type holding a length and
a base (or a trait `Scope` that `LocalCtx` implements), so that code which
has no syntax passes no syntax. Then the filler entries, `FILLER`,
`Eval::scope` and probably `CtxEntries::repeat` go away, and so do the
comments justifying them. A cheaper interim check is a filler entry whose type
cannot be mistaken for a real one, with a debug assertion where entries are read,
but the shape type is the real fix.

Found by the kernel comment audit ([[kernel-comment-audit]]).

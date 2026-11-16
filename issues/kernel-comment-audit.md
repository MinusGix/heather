---
title: Cut the kernel's comments to the ones that carry a reason
status: open
labels: [kernel,code-health,docs]
area: kernel
created: 2026-11-16
updated: 2026-11-16
---

Fewer comments in `crates/kernel`, each one worth its lines. The rule Minus
agreed (2026-11-16): **the reason stays, the story goes.** A comment keeps
what a reader of the code needs (why this and not the obvious thing, a
soundness argument and its limits, the rule of the paper it implements, why
a budget is that size). It loses how the code came to be: round and stage
numbers, dated history, closed-issue narratives, concrete timings (they go
stale; costs are stated as shapes), and counts like "the seventh copy".

A comment that justifies a hack is a finding, not a comment: the hack gets
an issue with its fix, and the comment shrinks to a link.

## Found so far

- [[fold-probe-nested-probe-variable-collision]]: a probe-level comment
  ("Γ is never this deep") hid a proof of `False`. Fixed.
- [[kernel-filler-contexts]]: β helpers fed filler Γs typed `Nat`.
- [[kernel-binder-count-tables]]: three hand-written binder-count tables kept in sync by review.
- [[kernel-vestigial-apis]]: `Level::join`, test-only `bit_run_cons`.

## Plan

1. Outdated or wrong comments fixed (stale counts, dead links, contradictions).
2. History and noise cut, one file per commit, kernel PRs for Minus to merge.
3. A full read of the five large files (`term`, `typing`, `conv`, `eval`,
   `value`), which the first pass only keyword-swept.

## Log

- 2026-11-16: Pass 2 (PR #684): full read of value/eval/conv/typing/term — nine docs on the wrong item moved, conv's 36-copy out-of-line note stated once, [[slug]] links in code replaced by issue paths. Citation sweep: 79 issue files cited from crates/kernel/src, all exist; 67 closed, none cited as if still pending; of the 12 open, conversion-typed-eliminator-congruence had landed in full and is closed.

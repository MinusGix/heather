---
title: The LGG's mismatch diagnostic prints raw kernel terms, unreadably
status: open
labels: [frontend,diagnostics,elaboration]
created: 2026-08-18
updated: 2026-08-18
---

`crates/elab/src/lgg.rs`'s `mismatch` builds its message with `{x:?}` on four
kernel `Term`s — the two sides at the differing position and the proof's two
endpoints. At a `Nat` goal that reads fine. At a **lowered inductive** it is a
wall of `inl[0,0](Σ[0,0](Unit 0). …)` several thousand characters long, four
times over, and the one thing the reader wants — *which subterm of my goal did
not match my proof* — is not recoverable from it.

Found while diagnosing [[congruence-by-anti-unification]] (2026-08-18): every
`cannot generalize` failure in `lib/std/int.hthr` and `lib/std/list.hthr`
produced one, and reading them required a script to slice the string.

`Debug` on kernel terms is budget-bounded and that is working as designed — the
bound is what stops this being an OOM. The defect is that a *user-facing
diagnostic* uses `Debug` at all.

## What it assumes from elsewhere

- `crates/elab/src/display.rs` can spell a `Type` (`spell_type`) and has no
  term-level counterpart. Assumed here: only that a term printer does not exist
  today, so this cannot be fixed by swapping one call.
- **[[display-inductive-type-arguments]]** owns what a lowered instance can say
  about itself. Assumed here: only that it is the same underlying gap — a
  lowered term does not remember its surface spelling.

## Shape of the fix

Two options, and the cheaper one may be enough.

1. **Say less.** The message does not need the four terms. It needs the
   *expected type* (which `spell_type` can already render) and a description of
   where the walk stopped — a path, or the head former of each side. Cheap, no
   new printer, and strictly more useful than the dump.
2. **A term printer.** The real fix, shared with every other diagnostic that
   currently cannot name a term, and the thing a lowered-inductive-aware
   display has to do anyway.

Take (1) as an interim only if (2) is not otherwise scheduled.

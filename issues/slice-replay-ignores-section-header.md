---
title: "A declaration replayed after an edit keeps the section header it was elaborated under"
status: open
labels: [cache,soundness,sections]
area: infrastructure
created: 2026-11-11
updated: 2026-11-11
---

Found 2026-11-11 while building `lib/std/algebra/fixpoint.hthr`
([[galois-connections-and-checked-fixpoints]]).

`heather check --cache` of an edited module replays the declarations whose
own text did not change ("N declarations replayed after an edit"). A
section's header is not part of what a member's replay is keyed on: after
the header gains an explicit binder, a member whose text is unchanged is
replayed with the signature it had under the old header, while the members
that were re-elaborated call it with the new one.

## Reproduction

1. A module with

   ```
   section<A: PartialOrderRel(≈, <=)> {
   fn PartialOrderRel::Monotone(f: A → A) → Type { (x, y: A) → x <= y → f(x) <= f(y) }
   theorem PartialOrderRel::t(f: A → A, m: PartialOrderRel::Monotone(f), x: A): f(x) <= f(x) { m(x, x, PartialOrderRel::le_refl(x)) }
   }
   ```

   checked once with `--cache`.
2. Change the header to
   `section<A: PartialOrderRel(≈, le)>(le as <=: A → A → Type) {` and the
   theorem's mention to `PartialOrderRel::Monotone(le, f)`, leaving the
   `fn` line as it is.
3. `heather check --cache` now refuses the theorem:
   "`PartialOrderRel::Monotone` is applied to too many arguments". The same
   file without `--cache` checks, and so does a fresh module with the same
   text. The refusal persists across cached runs until the `fn` line's text
   changes.

## Why it matters

Here it refused a correct module, which costs a confused hour. The other
direction is the concern: a member replayed under a header that has since
*lost* a binder or a constraint is a declaration the current source does not
state. The kernel has checked the replayed term, so nothing false is
proved, but the module that checks is not the module on disk, and the fast
and `--pr` lanes replay.

## Acceptance

- A member's replay key covers the headers of the sections that enclose it
  (binders, constraints, symbol aliases), or a changed header invalidates
  the members under it.
- A regression test beside `crates/elab/tests/slice_replay.rs`: the
  reproduction above, in both directions (a binder added and removed).

## What it assumes from elsewhere

- **[[declaration-slice-replay]]** owns slice replay and its keys.

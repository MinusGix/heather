---
title: Erased fields of a record a runtime fn takes: the arena's claims beside its laid words
status: open
labels: [ownership,native,reflector]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-24
---

`docs/language/ownership-design.md` §13.4 is settled for the arena by [[ownership-stores-and-keys]]: erased state a `mut self` method changes is an erased field beside the laid record (`Heap { arena, claims, ok }`, `lib/native/runtime/arena_handles.hthr`), not a parameter of its type. Today `Heap` is an ordinary record and its functions ordinary `fn`s; the compiled arena is still `Arena`'s `runtime fn`s.

What compiling `Heap`'s functions needs: the reflector dropping a record's erased fields (here `claims` and `ok`, never read by code, only by proofs) the way [[runtime-erased-parameters]] drops erased parameters, so a `mut self` method of `Heap` lowers to `Arena`'s words alone and its certificate is about them. Which fields are erased has to be stated somewhere the reflector reads (a mark on the field, or a type whose values have no layout).

## What it assumes from elsewhere

- **[[runtime-erased-parameters]]** owns dropping erased parameters. Assumed here: only that a dropped field is the same question one level in.

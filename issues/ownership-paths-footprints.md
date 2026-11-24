---
title: Footprints for paths beyond list indexes: record fields as byte spans, elements of windows
status: open
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-24
---

Footprints for paths beyond a list's indexes, so the apart decider reaches record fields and nested windows (residue of [[ownership-paths]]).

`lib/std/machine/list_path.hthr` decides `Apart` for paths into a list by their spans (`PathIn`, `Span::apart`). Three cases it does not reach:

- **A field of a laid record.** A `Part` (`lib/std/machine/part.hthr`) carries a byte offset and size with `reads` and `frames` laws: those are `PathIn`'s clauses over `List<u8>`. A `Part` read as a `Path<List<u8>, B>` at a base, with its `PathIn` at `Span(offset + at, size)`, would let `Span::apart` decide two fields apart from their layout (`Layout::fits_apart` already gives the premise). Today two fields of one element are apart only by their own `Disjoint` (`Apart::under`).
- **An element of a window.** A step `[A; n] → A` (a vector entry) composed after `Path::window(lo, n)` lies in `Span(lo + i, 1)`, not only in the window's span: `PathIn::then` gives the outer span, which is sound but loses the finer one. A `PathIn` for the composed step at the inner span is the missing lemma, and window-of-window normalisation with it.
- **Keys.** [[ownership-stores-and-keys]] owns a key as a path step; its footprint (the key itself) is a second kind of footprint beside spans, decided by key inequality as the word map's slots are (`WordMap::slots_apart`).

## Done when

A record's two fields, and an element of a window beside another window, are found apart by the decider with no proof written, at open and closed layouts, with a negative control each.

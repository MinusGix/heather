---
title: Footprints for paths beyond list indexes: record fields as byte spans, elements of windows
status: closed
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-25
---

Footprints for paths beyond a list's indexes, so the apart decider reaches record fields and nested windows (residue of [[ownership-paths]]).

`lib/std/machine/list_path.hthr` decides `Apart` for paths into a list by their spans (`PathIn`, `Span::apart`). Three cases it does not reach:

- **A field of a laid record.** A `Part` (`lib/std/machine/part.hthr`) carries a byte offset and size with `reads` and `frames` laws: those are `PathIn`'s clauses over `List<u8>`. A `Part` read as a `Path<List<u8>, B>` at a base, with its `PathIn` at `Span(offset + at, size)`, would let `Span::apart` decide two fields apart from their layout (`Layout::fits_apart` already gives the premise). Today two fields of one element are apart only by their own `Disjoint` (`Apart::under`).
- **An element of a window.** A step `[A; n] → A` (a vector entry) composed after `Path::window(lo, n)` lies in `Span(lo + i, 1)`, not only in the window's span: `PathIn::then` gives the outer span, which is sound but loses the finer one. A `PathIn` for the composed step at the inner span is the missing lemma, and window-of-window normalisation with it.
- **Keys.** [[ownership-stores-and-keys]] owns a key as a path step; its footprint (the key itself) is a second kind of footprint beside spans, decided by key inequality as the word map's slots are (`WordMap::slots_apart`).

## Done when

A record's two fields, and an element of a window beside another window, are found apart by the decider with no proof written, at open and closed layouts, with a negative control each.

## Log

- 2026-11-25: Discharged by [[ownership-library-join]] (2026-11-25, branch `claude/ownership-library-join`):

  - **A field of a laid record**: `lib/std/machine/part_path.hthr`. A codec read off its bytes is a step (`Stored::codec_path`); a stored value at `at` is the window of its size then that step (`Stored::path`), so its footprint `Span(at, size)` is `PathIn::then` of the window's, with no proof. `Part::path(p, at)` is the field's codec at `p.offset + at`, reading the field of the whole (`Part::path_reads`, from `reads`) and writing the whole with the field replaced (`Part::path_writes`, from `frames`). Two fields are decided apart by their spans (`Part::paths_apart`); at an open base the verdict is taken at base zero and shifted (`Part::paths_apart_at`, so a closed layout's verdict is still `trivial`); at open codecs from the layout (`Part::pair_apart`, by `Layout::offset_of_ge`). Lawful only where the codec is exact (`Stored::Exact`): a codec with padding writes its padding back as its own bytes, so writing back what was read is not the identity there. Apartness needs no exactness.
  - **An element of a window**: `lib/std/machine/vector_path.hthr`. `Path::in_vector` reads a length-keeping list path in a vector, so `[A; n] → A` is `Path::entry(n, i, pad)` = `elem(i)` read in the vector. `PathIn::under_window`: a path in `s` under the window of `n` from `lo` lies in `Span(lo + s.base, s.len)`; `PathIn::window_entry` (`Span(lo + i, 1)`) and `PathIn::window_of_window` (`Span(lo + lo2, m)`) are its instances. The normalisation is of footprints, which is what the decider reads; the two spellings are not one path where the outer window does not fit and the inner one would, so no value-level equation is owed.
  - **Keys**: `KeyIn` in `lib/std/data/store_path.hthr`, decided by `Key::apart` (`KeyIn::apart_sound`).

  Done-when met: probes `lib/_tests/std/machine/part_path_tests.hthr` (a header's tag and length apart with `trivial` at base 0, length and flags at an open base with `trivial`, a flag at an open index by `omega`, the pair at open codecs; negative: a field not apart from itself, the whole beside a field refused) and `lib/_tests/std/machine/vector_path_tests.hthr` (elements of windows at closed spans by `trivial`, at open sizes by `omega`; negative: overlapping elements not apart, the decider refusing them).

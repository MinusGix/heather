---
title: Paths and validity: the meaning of a live borrow, with split_at_mut and the word map's slot as theorems
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-24
---

The meaning layer of `docs/language/ownership-design.md` §10.4 and §10.6: a live path is data that names a part of an owner, with a partial read and a partial write. Pure library work; nothing in the compiler changes.

## Scope

- **Paths as data.** Steps for a record field, an element of an array or vector at an index, and a window of a span, composed; a path's partial `get` and `set` on its owner, and its denotation as a `Location` (`lib/std/machine/location.hthr`) where it is total. This is the partial-access bridge and the composition of law records that [[state-location-and-frame-kit]] leaves owed.
- **`Valid(owner, path)`** as a proposition with a decider on the steps above, and the lens laws under it.
- **`Apart(p, q)`** with a sound decider on index and window steps, giving `Disjoint`: stores commute and each keeps what the other reads.
- **What an operation keeps.** A statement that an operation on an owner keeps a path valid, and that it keeps what the path reads; proved for a store through another path, and for a vector's push with spare capacity. A growing push does not keep paths, stated as a `¬` theorem.
- **Worked examples as theorems** (§6 of the design): splitting an array at an index gives two paths that are apart and whose stores rebuild the whole (`split_at_mut`); holding element `i` while storing element `j ≠ i`; the word map (`lib/native/runtime/word_map.hthr`): the slot of a key as a path, with `get` and `insert` stated as its read and write under `WordMapInv`.

## Done when

The module and its probes pass the library gate, each example above is a theorem a client could cite, and each negative control is a `¬` theorem or a named refusal. The design note's §10.4 and §10.6 are corrected where the work shows them wrong.

## What it assumes from elsewhere

- **[[ownership-discipline-over-code]]** owns the judgment that will raise `Valid` and `Apart` as requests. Assumed here: only that they are ordinary propositions.
- **[[ownership-stores-and-keys]]** owns keys into a store; a key is one more kind of path step, added there.

## Log

- 2026-11-24: Built, as library only (no compiler change):

  - `lib/std/machine/path.hthr`: `Path<S, V>` (partial read, total write that changes nothing where the path is not valid) with `PathLaws`, the optional-lens laws, holding at every owner. `Path::Valid` is "the partial read answers" (`Exists a. p.get(s) = Some(a)`), decided (`valid_dec`, Bool `valid` with `valid_sound`/`valid_complete`). Locations and total paths convert both ways with their laws (`of_location_laws`, `location_laws`); paths compose (`then`, `then_laws`); `compose_location_laws` is the composition of law records [[state-location-and-frame-kit]] owed. `Apart` (partial `Disjoint`) with `symm`, `of_disjoint`, `disjoint`, `both_read`, `under` (two parts apart inside one part). `Path::Keeps(before, after)` with `keeps_valid`, `Apart::keeps`, `not_keeps`.
  - `lib/std/machine/list_path.hthr`: `Path::elem(i)`, `Path::window(lo, n)` (value `[A; n]`), lawful and valid exactly where they fit; `PathIn(p, span)` footprints, kept by composition (`PathIn::then`); the decider `PathIn::apart_sound` from `Span::apart`. Examples: `split_apart`, `split_valid`, `split_rebuilds`, `split_reads` (split_at_mut), `hold_while_store`. Negative controls: `elem_not_apart_self`, `overlap_not_apart`, and the probe's named refusal of the decider on overlapping windows.
  - `lib/native/runtime/word_map_paths.hthr`: `WordMap::slot_path(k)`, lawful at every table (`slot_laws`); under `WordMapInv`, `get_is_slot` and `insert_is_slot` (get and insert of a stored key are its read and write); `slots_apart` for different keys; `insert_keeps_other`; negative control `slot_not_apart_self`.
  - `lib/native/runtime/arena_paths.hthr`: `Arena::elem_path(h, b, i)`, lawful, valid below the length under `VecInv` (`elem_valid`); `push_in_keeps` (a push with room keeps every path); `grow_loses`, `grow_not_keeps` (growing keeps none).
  - `lib/std/data/vector.hthr`: `vector_update_self`, `vector_update_update_same`, `vector_update_update_apart` (own commit).
  - Probes: `lib/_tests/std/machine/{path,list_path}_tests.hthr`, `lib/_tests/native/runtime/{word_map_paths,arena_paths}_tests.hthr`.

  Decided on the way, recorded in the design note (§10.4 "Built", §10.6 "What the vector showed", §13.7):
  - The partial write is total (a no-op where invalid), so the laws hold at every owner and validity is about the read alone.
  - A window's value is `[A; n]`: a write cannot change the shape, and the empty window past the end is not valid (Rust's `xs[5..5]` of four panics).
  - `Apart` is a fact about the meaning; spans decide it (sound, complete on spans only). Fields of one element are apart by `Apart::under`, not the decider.
  - Correction to §10.6: every push keeps a path into the vector's *value*; what a growing push breaks is a path that names the home, which is what a pointer is. So the arena's element path carries the window it was taken in, and validity is stated over the home.
  - `Keeps` is a relation between two owners, so an operation with a precondition (room) states what it keeps under it.
  - Laid out in new modules rather than `word_map_laws.hthr`/`arena_laws.hthr`, to stay out of the files other packages edit. `arena_paths.hthr` cites `Arena::push_in`, `grow`, `copy_at` and `VecInv`, `copies`, `grow_eq` from `arena_laws.hthr`: if [[ownership-stores-and-keys]] renames those, this module follows.

  Residue: footprints beyond list indexes (record fields as byte spans through `Part`, elements of windows, keys) filed as [[ownership-paths-footprints]]. `Arena::push` itself has no branch equations (arena.hthr says why), so the growing push is stated at its `grow`.

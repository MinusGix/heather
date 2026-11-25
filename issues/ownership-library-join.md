---
title: Join the first wave's libraries: a key as a path step, footprints for fields, the separation algebra at paths
status: open
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The first wave built three libraries side by side: paths (`lib/std/machine/path.hthr`, `list_path.hthr`), stores and keys (`lib/std/data/store.hthr`, `lib/native/runtime/arena_handles.hthr`) and the separation algebra (`lib/std/algebra/pcm.hthr`, `lib/std/data/set/access_map.hthr`). Each filed the join with the others as residue. This issue is that join, taken as one round so the statements meet.

## Scope

- **A key is a path step.** `Store::key_path(k) : Path<Store<V>, V>` with its laws, `Path::Valid` of it stated as `Store::Valid` (the equivalence `Store::valid_exists` / `exists_valid` is there), keys apart by inequality, and `then` composing a key with a path into the value. The arena's window (`Heap`, `Window`) and the paths package's `Arena::elem_path` (`lib/native/runtime/arena_paths.hthr`) stated over one notion, so an element of a vector held by handle is a key step then an index step.
- **Footprints beyond list indexes** ([[ownership-paths-footprints]]): a laid record's `Part` as a path with a byte-span footprint, an element inside a window at its own span, and keys as a second kind of footprint.
- **The separation algebra at paths** ([[separation-algebra-paths-instance]]): the `Pcm` instance whose carrier is paths held with shares, composing where `Apart` holds; the frame theorem with an `Access` frame; a decider for `Access::Valid`.
- **`arena-handles-push-and-new-vec`** if it falls out: push and new-vector over handles, now that `Arena::store` is a `runtime fn` answering `Mutated`.

## Done when

A vector element reached through a handle is one composed path with one validity statement and a footprint; two such elements, and two fields of one record, are decided apart; the path-level frame theorem is proved and cites the algebra; and the three residue issues are closed or say exactly what is left.

## What it assumes from elsewhere

- **[[ownership-paths]]**, **[[ownership-stores-and-keys]]**, **[[separation-algebra-ownership]]** own what they built; this issue changes their statements only to make them meet, and says so where it does.

## Log

- 2026-11-25: Built (2026-11-25, branch `claude/ownership-library-join`), library only:

  - **A key is a path step** (`lib/std/data/store_path.hthr`, probes `lib/_tests/std/data/store_path_tests.hthr`): `Store::key_path(k)` (read `s.get(k)`, write `s.put(k, v)`), lawful at every store (`key_laws`, over new slot and store lemmas `Slot::written_read`, `written_none`, `written_twice`, `written_other_answer`, `written_commute`, `Store::put_read`, `put_none`, `put_put`, `put_get_other`, `put_commute`); validity the store's (`key_valid`, `valid_of_key`, `key_reads`); keys apart by inequality, of different slots or one slot at two generations (`keys_apart`); the decider `Key::apart` (sound: `keys_apart_sound`; complete: `key_apart_complete`, from `key_not_apart_self`); what the store's operations keep (`alloc_keeps_path`, `put_keeps_path`, `free_keeps_path`, `free_ends_path`); a key then a path into its value (`key_then`, `key_then_laws`, `key_then_valid`, `key_then_valid_key`, `inside_apart`); keys as a footprint (`KeyIn`, `KeyIn::of`, `Store::key_in`, `KeyIn::apart_sound`).
  - **Path tools** (`lib/std/machine/path.hthr`, additions only): `PathSame` (one path spelled twice; `PathLaws::respects`, `Path::valid_respects`, `Apart::respects`, `PathSame::guard`, `PathSame::after`); `Apart::then_both` (parts of parts apart); `Path::then_assoc`; `Path::guard` (a path behind a check) with `guard_laws`, `guard_valid`, `guard_valid_on`, `guard_valid_inner`, `guard_then`, `guard_apart`.
  - **Vectors and windows** (`lib/std/machine/vector_path.hthr`, probes `lib/_tests/std/machine/vector_path_tests.hthr`): `Path::in_vector` (`in_vector_laws`, `Apart::in_vector`, `in_vector_then`); `Path::entry(n, i, pad)` (`entry_laws`, `entry_valid`, `entry_inside`, `entries_apart`); `Path::under_window` with `PathIn::under_window` (a path under a window at its own span), `PathIn::window_entry`, `PathIn::window_of_window`, `Path::window_entry_reads`, `Path::window_entries_apart`.
  - **A vector element held by handle** (`lib/native/runtime/arena_handle_paths.hthr`, probes `lib/_tests/native/runtime/arena_handle_paths_tests.hthr`): the key step `Heap::window_path(w)` (the words behind `Heap::holds`, which decides `Heap::Valid`: `holds_sound`, `holds_complete`), lawful (`window_laws`), valid exactly where the handle is (`window_valid`, `valid_of_window`); the element `Heap::elem_path(w, i)` = key step then `Path::entry`, with one validity statement (`elem_valid`, `elem_valid_parts`), its footprint (`elem_same`, `elem_run_in`), decided apart (`elems_apart`, `valid_elems_apart`, `elems_apart_in`); the handle's read and store are the path's (`elem_reads`, `read_is_elem`, `store_is_elem`); a vector's element (`Heap::vec_elem`, `vec_elem_valid`, `vec_elem_items`, `vec_elem_agrees` with `Arena::elem_path`, `vec_elems_apart`).
  - **Record fields** (`lib/std/machine/part_path.hthr`, probes `lib/_tests/std/machine/part_path_tests.hthr`): `Stored::codec_path`, `Stored::path` (`path_laws` where exact, `path_in`, `path_get`, `path_set`, `path_valid`, `path_fits`), `Part::path` (`path_laws`, `path_in`, `path_reads`, `path_writes`), `Part::paths_apart`, `Span::apart_shift`, `Part::paths_apart_at`, `Part::pair_apart`.
  - **An allocation's footprint owned exclusively** (`arena_handle_paths.hthr`): `Held::owns_compose`, `Heap::valid_owns`, `Heap::alloc_owns`, `Window::span`; the arena half of [[separation-algebra-ownership]]'s done-when.
  - **The algebra at paths** (`lib/std/data/set/held.hthr`, `lib/std/machine/access_frame.hthr`, probes `lib/_tests/std/data/set/held_tests.hthr`, `lib/_tests/std/machine/access_frame_tests.hthr`): `Held` with `Pcm<Held>`, the decider `Held::valid` (`valid_sound`, `valid_complete`), `Held::own`, `Held::at`, `own_excludes`, `view_refuses_store`, `views_compose`; `Held::apart_of_valid`, `Held::key`, `keys_apart_of_valid`, `inside_apart_of_valid`; the frame theorems `Held::path_keeps`, `path_keeps_sep`, `view_kept`, `local_of_span`, `Access::store_keeps`, `Access::store_keeps_sep`, `Held::store_keeps`.

  **First-wave statements changed: none.** Every join was reachable by adding: `Store::Valid` already had its `Exists` form (`valid_exists`/`exists_valid`), `Heap::Valid` is the claims' key read with agreement, and `Part` already carried `reads`/`frames`. `arena.hthr` and `arena_laws.hthr` untouched; nothing was renamed (`Key`, `Store` included).

  Decided on the way (recorded in `docs/language/ownership-design.md` §10.4 "Joined", §10.7 "Joined with the separation algebra", §12, §13.7, and `docs/library/separation-algebra-design.md` §6–§7):
  - A handle's validity enters a path as a guard (`Path::guard`) whose check reads only the claims, which no word write changes, so the guard keeps the laws and `Apart`; not as a composition through the claims store, whose key reads a claim, not the words.
  - Two spellings of one path are a relation (`PathSame`), not an equation: paths are records of functions and the kernel has no function extensionality.
  - The steps into a vector are the list's steps read in it (`Path::in_vector`), not a second family; window-of-window "normalisation" is of footprints, which is what the decider reads (the two spellings differ as paths where the outer window does not fit).
  - A field's path is a window then the codec read off its bytes; lawful only for an exact codec, apart for any.
  - The separation algebra's carrier at paths is footprints held at shares, not paths: `Apart` has no general decider and paths no decidable equality. Composition is sound for `Apart`, not complete. A key's footprint is its slot, in a second address space; a resource holding both is `Pcm::product`.
  - Deciders and where each is complete: `Key::apart` complete (where it says no the keys are one key, not apart from itself); `Held::valid` complete; spans (`PathIn::apart_sound`, `Part::paths_apart`, `Heap::elems_apart`) complete on spans, not on paths: two guarded paths whose checks never pass at one heap (a stale window's element and the fresh window's over the same word: one claim slot, two generations) do not meet, yet their spans do, and the probe records the decider refusing them.

  `arena-handles-push-and-new-vec` did not fall out of the join; it stays open, narrowed to what it needs. Residue filed: [[held-endpoint-decider]].

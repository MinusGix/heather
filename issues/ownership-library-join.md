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

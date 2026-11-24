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

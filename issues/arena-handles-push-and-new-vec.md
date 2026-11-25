---
title: Push and new_vec over the arena's typed handles
status: open
labels: [ownership,native,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-25
---

[[ownership-stores-and-keys]] restated the arena's window laws and `grow` over typed handles (`lib/native/runtime/arena_handles.hthr`: `VecHandle`, `VecOk`, `Heap::grow` with `grow_keeps`, `grow_items`, `grow_ok`). Not restated yet:

- **`new_vec`**: allocating the header and the data window (as two claims) and writing the header's words, answering a handle with its `VecOk`. The probe builds one by hand at closed values (`lib/_tests/native/runtime/arena_handles_tests.hthr`); the open-heap version needs a lemma that three stores into the header window read back as the cells `VecOk` names (word reads against `Arena::cell`).
- **`push`**: `push_in_abs` over handles (a push with room appends and keeps every other window), and `push` as `push_in` or `grow` then `push_in`.

## What it assumes from elsewhere

- **[[ownership-stores-and-keys]]** owns `VecOk`. Assumed here: only its fields.

## Log

- 2026-11-25: [[ownership-library-join]] (2026-11-25) did not build these: they did not fall out of the join. What the join gives them: a vector's element is a path (`Heap::vec_elem`, `lib/native/runtime/arena_handle_paths.hthr`) reading the vector's item (`vec_elem_items`) and what `Arena::elem_path` reads (`vec_elem_agrees`), and `Heap::store` is a path write (`store_is_elem`). What is still needed, narrowed:

  - **`push_in` over handles**: `Heap::push_in(h, v, ok, x)` writing the arena by `Arena::push_in` (a `mut self` runtime fn answering `Mutated`) and keeping the claims; it needs `Arena::push_in(...).after` to keep `top` and `limit` (read off `Arena::push_in_eq` in `arena_paths.hthr`, which states the after-arena under `VecInv` and room) so `HeapInv` carries across, and a `VecOk` after (header words: base and capacity unchanged, length one more and within capacity). Then `push_in_keeps` (arena_paths) restated as every `Heap::vec_elem(v, i)` below the old length kept, through `vec_elem_agrees`.
  - **`new_vec`** and **`push`** as before.
- 2026-11-25: [[runtime-record-calls-erased]] (2026-11-25) lets a compiled function of `Arena` call the window's `read` and `store` with found proofs (ledger row `Arena::port_bump`: the caller carries the window's fit as its own proof and tests the index). `Heap`'s operations over handles did not fall out: `Heap` is an ordinary record whose `claims` and `ok` fields are erased state no layout holds, so compiling a `Heap` method needs the reflector to drop a record's erased fields, [[runtime-record-erased-fields]]; with that, a `Heap` push would call `Arena::store` with a proof read off `VecOk` the way `port_bump` passes its `fits`. Also in the way of a push written through `store`: `bv_omega` does not read `base + len < 16` through a sum of words that may wrap, so the proof has to come from the handle's invariant (a natural-number fact) rather than a test in the code.
- 2026-11-25: The `bv_omega` limit met here is taken up as [[bv-omega-fits-through-wrapping-sum]]: the implication from a word sum's test to the natural-number fit is false where the sum wraps, so that issue classifies the true spellings and adds the check whose answer gives the proof. Erased fields are [[runtime-record-erased-fields]], started the same day.

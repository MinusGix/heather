---
title: Push and new_vec over the arena's typed handles
status: open
labels: [ownership,native,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-24
---

[[ownership-stores-and-keys]] restated the arena's window laws and `grow` over typed handles (`lib/native/runtime/arena_handles.hthr`: `VecHandle`, `VecOk`, `Heap::grow` with `grow_keeps`, `grow_items`, `grow_ok`). Not restated yet:

- **`new_vec`**: allocating the header and the data window (as two claims) and writing the header's words, answering a handle with its `VecOk`. The probe builds one by hand at closed values (`lib/_tests/native/runtime/arena_handles_tests.hthr`); the open-heap version needs a lemma that three stores into the header window read back as the cells `VecOk` names (word reads against `Arena::cell`).
- **`push`**: `push_in_abs` over handles (a push with room appends and keeps every other window), and `push` as `push_in` or `grow` then `push_in`.

## What it assumes from elsewhere

- **[[ownership-stores-and-keys]]** owns `VecOk`. Assumed here: only its fields.

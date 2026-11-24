---
title: A run-time generation for the arena's windows, so its checked access is a word compare
status: open
labels: [ownership,native,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-24
---

[[ownership-stores-and-keys]] built the arena's windows as typed handles whose validity is a key into erased claims (`lib/native/runtime/arena_handles.hthr`, `docs/language/ownership-design.md` §10.7 "Built"). The static route (a proof of `Heap::Valid`) is complete. The checked route is not built for the arena: the claims are history, so keeping them at run time is a table, not a word compare.

The generic store has the compare (`Store::check`, a slot's generation against the key's, `check_decides`); the arena needs the same layout: a generation word per window in the heap (Vale's), bumped by `reset` for each window it ends, carried in the window handle, and a `checked` read that compares it and is proved to decide `Heap::Valid`. That changes `arena.hthr`'s layout and its compiled functions, which is why it was left (the arena's `read` and `store` were being moved to `runtime fn` by [[runtime-erased-parameters]] in the same wave).

## What it assumes from elsewhere

- **[[ownership-stores-and-keys]]** owns `Heap::Valid`. Assumed here: only that the checked access must decide it.

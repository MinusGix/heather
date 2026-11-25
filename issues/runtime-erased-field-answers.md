---
title: An answer carrying an erased field: Heap::alloc's Grant and Heap::grow's VecHandle compiled
status: open
labels: [ownership,native,runtime-fn]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

[[runtime-record-erased-fields]] compiles a `runtime fn` whose record is a plain record of one laid field and erased fields (`Heap`), and a record parameter of words and erased fields (`Window`). It does not compile a function whose *answer* carries an erased field: `Heap::alloc` answers `Mutated<Heap, Grant>`, where `Granted(window)` holds a `Window` whose `key: Erased<Key>` is the new claim's key, and `Heap::grow` answers a `VecHandle` of two windows. The code's answer would be the answer's words with the erased fields dropped (a `Grant` as the arena's `Alloc`: a tag and a base, the count being the size asked for), and the statement the answer read back at those words beside the function's own erased values.

What it needs: the result side of the reading (`rt_held_result`, `runtime_words_out`) taking a record or an enum's payload whose fields are words and erased ones, and the published agreement stating the answer's word fields (the projection `HWorld::through` already drops the record's erased fields; the answer's need the same, field by field, which is a statement of an enum's payload, not only a record's). `Heap::alloc` is also written as a `match` over the arena's answer with its equation (`alloc_by`), which the laid-record reflector reads as a call of an ordinary function; it would be written as the arena's call and a branch on its tag.

## What it assumes from elsewhere

- **[[runtime-record-erased-fields]]** owns reading a record with erased fields as its laid field. Assumed here: its `FieldWord`/`FieldErased` reading of a record parameter, which an answer would mirror.

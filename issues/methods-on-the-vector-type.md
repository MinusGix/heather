---
title: `[A; n]` has no name a method can be declared on
status: open
labels: [surface,methods,vectors]
area: language
created: 2026-11-13
updated: 2026-11-13
---

```heather
fn Vec::at({w, n: Nat}, self v: [BitVec(w); n], i: u64, …) → BitVec(w) { … }
// `Vec` is not a type, a type former or a function in scope, so `Vec::at` attaches to nothing —
// a member declaration is `fn <Type>::at(…)` …, and the owner must be declared (or be a kernel type) before it
```

A member's owner is a declared type or a kernel type with a name, and `[A; n]` has none in the surface. So the vector library is free functions (`vector_index`, `vector_update`, `vector_get`, `vector_entries`, …) and `v.at(i)` cannot be written. Minus (2026-11-13, PR #551's thread): `vector_at`, `vector_put`, `vector_get` "should obviously be on the type".

**Decided (Minus, 2026-11-13): the owner is `Vec`.** The host already views `[A; n]` as `Vec` of the element type and the length (`docs/host-elaboration-interface-design.md` §28), so `Vec` is the candidate: `fn Vec::at<A>({n: Nat}, self v: [A; n], …)`, called `v.at(i)`.

Then: the vector library's functions become methods (`vector_index` to `Vec::index`, and so on), a rename across `lib/`.

## Done when

A method declared on the vector type is called with a dot, and `lib/std/data/vector.hthr`'s functions are methods.

## Log

- 2026-11-13: Filed with the refusal above.
- 2026-11-13: Minus (2026-11-13): the owner's name is `Vec` ("could be confused with Rust `Vec`", and he would rather it were less of a kernel type too, but `Vec` will work). To be built in a side thread; moving `vector_at`/`vector_put`/`vector_put_byte_be` onto it follows in the indexing thread, with the found-proof lifting reading a method call.
- 2026-11-13: Minus ruled the owner is `Vec` (accepting that it may read as Rust's `Vec`). Built: `[A; n]` owns the namespace `Vec`, so `fn Vec::m(…, self v: [A; n], …)` declares and `v.m(…)` / `Vec::m(v, …)` call it; a file's own type named `Vec` keeps its members apart by subject (docs/receiver-member-resolution-design.md §9; probes `lib/_tests/std/data/vector_methods_tests.hthr`, `vector_owner_clash_tests.hthr`). Left: moving `vector.hthr`'s and `stored_words.hthr`'s functions onto the type, which the SHA-256 thread does on its own branch.
- 2026-11-13: PR #607: the three index functions are methods of the vector type now (`Vec::at`, `Vec::put`, `Vec::put_byte_be`, `lib/native/runtime/stored_words.hthr`), called `t.f.at(i)`, and SHA-256 and the probes are written that way. The tactic host names a global by its last part alone (`Elaborator::global_name_at`), so the record-function reflector tells `Vec::put` from a record's own `put` by the receiver being an array field. Left: `vector.hthr`'s own functions (`vector_get`, `vector_update`, `vector_index`) are still free functions.

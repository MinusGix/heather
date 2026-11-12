---
title: Classes in the layout library: a codec's compiled accessor, and a declared type's layout
status: open
labels: [native,layout,design]
area: heather-in-heather
created: 2026-11-12
updated: 2026-11-12
---

Minus, asked what records of functions (`Stored`, `Part`) are good for (2026-11-12): "why aren't they typeclasses then?" Two associations in the layout library are canonical enough to be classes, and both are done by name today. A prototype of each checks (`docs/layout-design.md` §10.2; the files are in the project's shared folder, `layout-prototype/cls.hthr` and `cls2.hthr`).

**A codec to its compiled accessor**, keyed by the codec's term as `Compile(f)` is keyed by `f`: `class Accessor<A>(codec: Stored<A>)` holding the `runtime fn` that reads the codec's value under a span's length word, the one that stores it, and the two theorems that tie them to `get` and `put` (`lib/native/runtime/stored_words.hthr` has all four for the big-endian words, as plain declarations). Probed: two instances at one type (`Stored::u32_be()`, `Stored::u32_le()`) are told apart by the term, resolution finds the instance from the codec passed, and a codec with none is refused as "no instance". This is what stage B's reflector reads to choose a field's load and store (`docs/layout-design.md` §9.4), and it is open: a new codec comes with its accessor.

**A declared type to its layout**: `class Lay<T>` with the instance `laid record T` declares. Probed: an instance for a record, a pair's derived from its parts', `size_of<T: Lay>()`, a `read_at<T>` with its law, sizes and bytes by `refl`. The generator would then find a field of type `R` by resolution, where it looks up the name `R::stored`.

What stops the second short: an instance is keyed by its class and its carrier's head (`docs/instance-resolved-key-design.md`), so `BitVec(8)`, `BitVec(32)` and `BitVec(64)` cannot each have one. Words need one instance at every width: a codec of a `BitVec(n)` at any `n` (whole bytes, the value resized, `Stored::be_bytes(k).map(resize, resize, …)`). That is not `Stored::u32_le()` by conversion at 32, so either the words' theorems are restated over it or the instance chooses by cases on the width and reduces to the library's codec at 8, 16, 32 and 64. And an instance is one byte order (the machine's); a declaration that wants another names it, as now.

Not built. The first class is wanted by stage B round 3 whichever way the rest is decided. The second waits on Minus's answer and on the words' instance.

Done when: the accessor class exists with instances for the library's words and the reflector uses it; and either `laid record` declares a `Lay` instance and reads nested fields through it, or this says why types stay found by name.

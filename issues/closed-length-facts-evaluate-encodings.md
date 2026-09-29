---
title: Closed facts about a generated program's length evaluate its encodings
status: open
labels: [elaboration, performance, native]
code: crates/cli/src/native/read_loop.rs @ 357c0afa
created: 2026-09-29
updated: 2026-09-29
---

A certificate's size facts over the 15 KB `wc` program ran past every CPU
rail, although the code equality they build on (`_code_written`) checks in
milliseconds:

- `_code_fits`, `Nat::leb_sound(232 + (spelled).len(), 65536, trivial)` over
  the code spelled with the formatter's `_lit()` trees: over 300 CPU-s for one
  declaration (20+ CPU-minutes for the image facts together).
- A generated chain of `List::len_append` steps over the same closed pieces,
  each `trans(len_append(p, rest), cong_fn(λ n => p.len() + n, …))`: over
  120 CPU-s, where the terms line up syntactically.

Unattributed. The hypothesis is that unification or a whnf probe
([[elaborator-whnf-probes-on-computing-types]]) meets a closed Nat sum and
evaluates it, which unfolds `structured_bytes` and runs the encoder on the
formatter's three copies ([[conversion-cost-at-large-values]] is the closest
closed relative).

Worked around (docs/native-wc-design.md §6.1): `read_fields_code_len` proves
the length once over open parts in the library, and the certificate
instantiates it with the formatter's `_byte_length` lemmas.
`image_facts`'s other path, reading the length off the spelled code, is
still what `--read-loop` and `--print` use: cheap at their sizes, and the
same trap once their tails grow. [[structured-lowering-code-size]] would
shrink the evaluation, not remove it.

Next: `--timings` on a cut certificate with only `_code_split` restored, and
the value-machine counters, to find which step evaluates.

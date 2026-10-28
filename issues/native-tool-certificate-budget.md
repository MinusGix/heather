---
title: Split write-elf's lowering and entry refls so tools past cat FILE fit the fuel
status: open
labels: [native,x86,performance]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-28
updated: 2026-10-28
---

Two of `write-elf`'s certificate statements are one kernel `refl` each,
under the kernel's fixed fuel (`DEFAULT_FUEL`), and both grow with the
tool. `cat FILE…` (round 7, [[native-compile-other-calls]]) is the first
tool to meet them, and fits only after trimming.

- **`<s>_elf_lowered_is`** (`{symbol}() = {p}_lowered()`): the builder's
  whole lowering (`Tool::source`, `lib/native/native_build.hthr`) evaluated
  at once. Its cost is linear in the tool's nodes times the leaf predicate
  run per node; `List::fits_registers` re-ran `leaf_checks`' register checks
  (constant truths for the pool's slices) and `nodes_inputs` four times, and
  `List::takes` re-tested the group. Dropping those cut cat FILE's lowering
  by about a third and it fits, without much margin. A tool past cat FILE's
  size (the §2 tools of `docs/native-real-programs-plan.md`: `wc`, `grep -F`,
  `sort`) will not.
- **`<s>_elf_entry`** (`lowered.entry(low) = {p}_at_N()`): a buffer's
  initial bytes are stored one `MOV/MOV/store` each, the address a full
  64-bit `low.add_nat(offset + i)`, all in the entry's one `refl`. A few
  thousand kernel steps per byte, so a tool's constant data is capped at
  a couple of hundred bytes. cat FILE's message table holds seven errnos
  for that reason (`cat_table` in `lib/native/native_tools.hthr`).

## Directions

- Split `lowered_is` the way `<s>_elf_e_*` split the emission: state the
  lowering of each statement part and join them, so no one `refl` holds the
  whole tool. The lowering numbers words in order (`next`) and packs leaves
  greedily, so a part's lowering depends only on its `next`; a lemma per
  `Act` constructor (`items` of `Seq` is the two parts' items) joins them.
- Incremental leaf predicate: carry the group's inputs and written ids
  through `packed_with` instead of recomputing them per node.
- Initial bytes: a cursor (one address, then `MOV AL`, store, `ADD RBX, 1`)
  or eight bytes a store, and the entry's `refl` cut per buffer; or the data
  page's bytes in the ELF file itself (loaded by Linux, no code), which
  [[native-data-capacity]] may want anyway.

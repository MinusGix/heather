---
title: Split write-elf's lowering and entry refls so tools past cat FILE fit the fuel
status: closed
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

## Log

- 2026-10-28: done; nothing in write-elf's certificate is one `refl` over
  the whole tool any more. Shares of the fuel below are cat FILE's.
  - **Lowering.** `List::packed` became a left fold, `List::pack` over a
    `Packing { done, group }` (`lib/native/native_build.hthr`), and nothing
    reads `done` until `Packing::stmt` closes it. So each part's statement
    quantifies over the statements before it:
    `(d) → a.packs(next, Packing(d, g)) = Packing(f(d), g')`, where `g` is
    the group open on entry (a literal read on the fork) and `f` prepends
    what the part closes. `lib/native/native_build_parts.hthr` joins parts
    with one lemma per `Act` constructor (`packs_seq_of`, `packs_let_of`,
    `packs_when_of`, `packs_while_of` with `pass_of`, `packs_do_while_of`)
    and `List::pack_append`; `Act::traced` reads every part's open group
    and closed statements on the fork, and `crates/cli/src/native/parts.rs`
    prints the statements (parts of up to a weight of nodes in one `refl`,
    chains of closed statements cut so each prefix definition stays
    small). Tools are written as `Tool`s now (`X_tool`, native_tools), so
    write-elf can see the `Act`. The largest piece is about a seventh of
    the fuel, and pieces don't grow with the tool. The old one-refl path
    stays for programs given as a `Source`.
  - **Entry.** A buffer's initial bytes are stated 32 at a time
    (`Prog::bytes_init_append`, `bytes_init_append_of`, `Prog::inits_of`,
    `Source::entry_of` in native_compile_correct), with the bytes as
    definitions `{p}_ib_j_k` and tails `{p}_it_j_k` so conversions compare
    names. Each chunk is about an eighth of the fuel at a few thousand
    steps a byte; the per-byte instruction cost itself is unchanged (a
    cursor or eight-byte stores remain an option if the chunk count
    matters).
  - **Allocation check** (the other one-`refl` statement, from
    [[native-allocator-cost]]): stated over the emission's parts,
    `{p}_ck_{id}`, with each statement's `out` and incoming live set as
    literals read on the fork (`Source::checked_spelled`), joined by
    `Stmt::checked_then_of`/`branch_of`/`repeat_of` and
    `Source::allocation_of`. Largest piece under a tenth of the fuel.
  - cat FILE's message table grew from seven errnos to twenty-six; the
    tools test gained a symbolic-link loop case (ELOOP) against GNU cat.
    The table's bytes roughly double the executable, since each initial
    byte is still a `MOV/MOV/store` in the entry, and write-elf's read of
    that long entry outgrew the suite's memory rail in one query; byte
    reads now go 256 items at a time (`emission::byte_reads`). Cheaper
    initial bytes (a cursor, eight-byte stores, or the bytes in the ELF
    file, [[native-data-capacity]]) would shrink both.
  - Still linear in the tool, each cheap per unit: `{p}_buffers_is`
    (the buffers' bytes), the holes' fills (the code's length), and the
    loop pass chains `{p}_k_*` (a loop body's closed statements, the
    largest about a tenth of the fuel at cat's loop).
  - The next wall is not the kernel: a probe of twice cat FILE's body in
    sequence runs the fork out of memory in the greedy allocator
    (`{p}_homes_spelled`), logged on [[native-allocator-cost]].

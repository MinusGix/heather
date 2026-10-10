---
title: Lay out native library code with labels, not hand-closed offsets
status: closed
labels: [native,x86,proofs,design]
created: 2026-10-07
updated: 2026-10-10
---

`lib/elf64_command.hthr` lays out its code by hand. Pieces are byte lists
whose lengths, offsets and jump displacements are literals: 165 `ca_` offsets
(`:95` on), 44 displacement constants and jump facts
(`cmd_d_failed_jmp() = BitVec::ofNat(4294966862)`, `cmd_j_*`), a `*_lens` list
and a `*_measured` theorem per segment, and `command_lens()` for the whole
(`:594`). Proofs cite code by offset and piece index (`pieces.operand(4)`), so
changing one instruction moves every later number and the proofs that name
them. The file says the numbers were generated; no generator is checked in.
The formatter does the same (`elf64_format_width.hthr:254`).

The producer mirrors the layout by string: `read_command.rs:51-80` restates
`command_parts` as 18 strings, names the long parts' own layouts, and its
`deep()` knows the formatter's internal shape. A renamed part is silently not
split.

Wanted: code as data with labels, and offsets computed.

```heather
inductive Asm { Block(List<Instruction>), Store(WordStore), Load(WordLoad), Label(Nat), Jcc(Cond, Nat), Jmp(Nat), Syscall, Splice(List<BitVec(8)>) }
fn label_at(prog: List<Asm>, l: Nat) → Nat
fn assemble(prog: List<Asm>) → List<BitVec(8)>
// once: each item's residency at its offset; each jump lands on label_at
```

Every near jump the native library emits is a fixed 5 or 6 bytes, so offsets
do not depend on displacements and one pass computes them. Acceptance:
`elf64_command` written over it with no literal offset, length or
displacement; the producer reads part boundaries from the program, and
`PARTS`, `SPLIT` and `deep()` are gone. Then the formatter, stat pass and
argument scan.

Cost to watch: a whole-file `assemble` cannot be evaluated in one
declaration's fuel; that is why the certificate joins long parts piece by
piece, and those joins are two thirds of the certificate
([[x86-certificate-per-declaration-constant]], 2026-10-05 log). The assembler
should emit per-item facts itself rather than evaluate the whole.

## What it assumes from elsewhere

- **[[x86-symbolic-fragment-layout]]** owns placement and symbolic references
  between fragments. Assumed here: only that labels inside one fragment are a
  compatible subset (this issue is a first customer for its interfaces).
- **[[native-wc-as-a-command]]** owns the command's layout as built. Assumed
  here: only that the binary may change byte for byte as long as `wc` stays
  certified.

## Log

- 2026-10-08: **Landed (first customer): `x86_64_asm`, and `elf64_command` written over it.**

  - **The assembler** (`lib/std/arch/x86_64/x86_64_asm.hthr`). Items are
    `Block`, `Code`, `Jcc`/`Jmp` to a named label, `Piece` (measured by its
    lemma), `Refer` (a library layout whose bytes take the labels' offsets,
    e.g. the read head and the write loop with their jumps out) and `Hole`
    (an open piece the program is assembled with: the scan at the letters and
    default, the spill table). A program is a chain of labels: a label is the
    program up to and with its item (`At(before, name, item)`), its offset is
    `prog_len(before)`. Once: `asm_resident` (each label's item resident at
    its offset, found from the end by depth), `asm_last_resident` (the
    open-ended last piece), `asm_len_is`, `asm_code_same` and `chunks_same`
    for producers.
  - **Why a chain, not the issue's list.** The kernel memoizes nothing across
    conversions, so an offset is evaluated afresh in every conversion that
    needs it. Over a list every offset is a sum of every length before it,
    and the command's proofs doubled their kernel steps that way (the first
    version of this round). Over a chain, the next label's offset is the
    previous one plus one item's length by definition, so the step a proof
    takes from one item to the next converts at the cost of one item,
    wherever it is. Forward jump targets cannot be labels (a later
    definition), so a jump names its target by number (`t_*`); a name given
    twice would misdirect a jump, which its landing fact then refuses.
  - **What the chain still costs.** A jump's landing is a closed equation
    between two offsets, and conversion meets the two sums against each other
    and runs out of fuel once a jump spans much of the program; the facts are
    proved by evaluation instead: `asm_jump_lands` (and `_back`) checks a
    jump item's landing as a Bool, `leb` both ways, with the item's offset
    bound once, and `refl` on `= True` leaves the evaluation to the kernel
    (an `IsTrue` proved by `trivial` had the elaborator evaluate it too).
    `asm_lands_forward`/`_back` do the same for a library piece's jumps. The
    hole check (`cmd_fits`) is stated unfolded for the same reason: elaborated
    against `FillsFit` the elaborator walked the whole chain. A proof helper that
    states an offset several items on (`k + 13`) has the same trouble, so the
    helpers state it an item at a time (`(k + 10) + 3`), as the labels are.
  - **`elf64_command`.** The 165 `ca_*` offsets, 44 displacement literals,
    the per-segment `*_lens`/`*_measured` and `command_lens()` are gone. The
    program is the `l_*` chain; `ca(l)`, `cmd_d(l)`, the jump facts and the
    write loops' `PrintJumps` are computed. Proofs cite `pieces(l_x())` and
    `ca(l_x())`; the proof bodies are otherwise unchanged.
  - **Producer** (`read_command.rs`). `PARTS`, `SPLIT`, `deep()` and `Tree`
    are gone. It evaluates `asm_lens(cmd_prog())` and the program's bytes,
    states each item where `asm_back` finds it, and states any item above the
    bound a fixed-size chunk at a time (`ChunksAre`: `take`/`drop`), which
    needs nothing of how the item is made: the scan, stat pass and rows are
    split without being named.
  - `near_rel` (x86_64_layout) is the displacement from a jump's end to a
    target; `wl_jumps` (elf64_write_loop) the write loop's own three jumps.

  Not done here: the formatter (`elf64_format_width.hthr:254`), the stat pass
  and the argument scan still lay themselves out by hand.

  Checked: `heather check lib/elf64_command.hthr`, and `build-x86
  examples/x86-native/wc.hthr wc_command` writes and kernel-checks the
  certificate through the new producer. Its chunked items keep the producer's
  declarations small; the issue stays open for the formatter, the stat pass and
  the argument scan.
- 2026-10-10: **Landed: the formatter, the argument scan, the operand cursor, the stat pass and the row writer are label programs.** Closes the issue.

  - Each module's code is an `x86_64_asm` chain (`lk_*`/`lp_*`/`le_*`/`lu_*`
    in the formatter, `lt_*`/`ls_*` in the scan, `lst_*`/`lc_*` in the
    cursor, `lw_*` in the stat pass, `lr_*` in the row). The per-segment
    `*_lens`, `*_measured`, literal offsets and displacement constants are
    gone; every jump fact is an `asm_jump_lands`/`_back` by evaluation, and the
    `*Pieces` records are `AsmPlaced` (format_width): a program's every label
    resident at its offset, from one `asm_resident`.
  - Repeated blocks (the formatter's count and digit blocks, the scan's letter
    slots) are parametric programs whose length is `prog_len` of one instance;
    their runs are proved per instance, so a block's index never enters an
    offset.
  - **One closed number per module: its size.** `scan_len`, `start_len`,
    `cursor_len`, `stat_len` and `row_len` are literals, each checked by
    `refl` against `prog_len` of its program (`*_len_closed`). With them
    computed, every command jump past the stat pass or the row evaluated those
    whole programs and five of the command's landing facts ran out of fuel. A
    change to a module's code fails at exactly that one theorem.
  - The scan's letter table and default block are `Hole`s, filled by
    `scan_fills`; a closed program is assembled with `no_fills()`
    (x86_64_asm).
  - The bytes are unchanged: `build-x86 examples/x86-native/wc.hthr
    wc_command` writes the same binary as before the round (same sha256).
  - The refusal tests' jump mutations are restated over labels (a condition
    inverted on a `Jcc` item, or a jump retargeted to a neighbouring label);
    a jump that lands "a byte late" can no longer be written in the source.
  - `x86_64_asm` now comes before the formatter in the embedded library and the
    command prefix (`FILTER_HALF` is one more).

  Cost: a cold `build-x86` of wc spends under a tenth more kernel steps than
  before the round, with misses and queries flat. The growth is in the scan's,
  cursor's and stat pass's own proofs (a landing or end-of-program fact
  evaluates the chain up to it) and in the certificate's statements of items
  made by `assemble`; no item changed rank.

  Residue, owned by [[native-straight-code-triples]]: the command's spill block
  (`spill_lens`, `elf64_command.hthr:65`) and the list layouts left in
  `elf64_read_pieces`, `elf64_read_filter` and `elf64_count_print`
  (`layout_code`/`layout_at`). They are straight code whose proofs that issue
  rewrites; they move onto labels with them.

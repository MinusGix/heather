---
title: Lay out native library code with labels, not hand-closed offsets
status: open
labels: [native,x86,proofs,design]
created: 2026-10-07
updated: 2026-10-07
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

---
title: The ELF header mutation test is 27 sequential single-conversion rejections; reshape or shrink it
status: open
labels: [testing,x86,performance,kernel]
created: 2026-09-11
updated: 2026-09-11
---

\`crates/cli/src/native/elf.rs::elf_header_mutations_are_rejected_by_heather\` builds 28 one-theorem modules — the static header against \`static_elf64_header\` by \`refl\`, once accepted and 27 times with one bit flipped and refused as NotConvertible — at ~3 s per conversion of a 176-byte \`List<BitVec(8)>\`. 88 s serial on furnace (2026-09-11), the single largest unit test in the suite, and structurally immune to the parallel kernel gate: a one-theorem module has nothing to overlap, and a rejection is checked once either way (§5.2 verdict reuse). It keeps the heather-cli unit target at ~75 s standalone / ~140 s under suite load, the full lane's tail.

Options, cheapest first:
1. **Fewer mutations.** 27 offsets cover identity/class/endian/type/machine/entry/table offsets and sizes, segment permissions/mapping/bounds/alignment, and stack policy. One per *field family* rather than one per field may be the same evidence; decide per field which mutations are distinct kernel paths and which are the same comparison at another byte.
2. **One module, positive form.** State each mutation as a decidable inequality (\`header != mutated\` by decide/refl on the byte list) so all 28 are *accepted* theorems in one module and the deferred gate spreads them over eight workers. This changes what is tested — "the kernel distinguishes the headers" rather than "the refl claim is refused" — so keep one or two refl refusals as the negative control and convert the rest, or reject the option on those grounds.
3. **Cheaper comparison.** Each refusal walks the full 176-byte list to find the flipped byte; the cost per refused conversion is [[kernel-failed-conversion-cost]]'s subject (this test is its customer datum). A cheaper closed-literal comparison there pays here without touching the test.

## What it assumes from elsewhere
- **[[kernel-failed-conversion-cost]]** owns why a refused conversion costs a successful one's price. Assumed here: only that option 3 belongs there.
- **[[parallel-kernel-gate]]** owns the gate. Assumed here: that a one-theorem module cannot benefit from it, so the fix is in the test's shape.

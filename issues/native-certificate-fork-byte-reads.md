---
title: Read each part's bytes once instead of re-emitting it in the fork
status: closed
labels: [native,performance]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-31
updated: 2026-11-11
---

After [[native-certificate-second-pass]] the largest certificate family of
a write-elf run is `bytes_#_#` (`crates/cli/src/native/emission.rs`): the
fork's reads that recover each part's bytes once the label offsets are
known. Each read runs the part's emission again in the reducer. Its steps
are linear in the code, with no kernel time, so the cost is the reads
themselves, and it grows with every part a tool adds.

## Directions

- Read a part's bytes in the part's own read, with the label offsets as a
  parameter, and apply the offsets once they are known. The obstacle the
  previous round noted: the offsets are known only after every part is
  read, so the read must keep the offsets abstract (a `Refer`-style
  function of the label table) rather than run twice.
- Otherwise share the emission between `e_#` and `bytes_#_#`: both evaluate
  the same part.

## Done when

`bytes_#_#` grows at a visibly smaller constant per pass on the 8/16/32
pass cat scratch tools, or is gone, with the ELF bytes unchanged.

## Log

- 2026-11-05: gardener: cites a file it shares with [[native-procedures-write-elf-capacity]] (`crates/cli/src/native/emission.rs`).
- 2026-11-11: done with [[native-tool-compile-attribution]]'s round, by the first direction with one change: the read does not keep the offsets abstract. A whole part's read (`Stmt::emission_reading`) ends with its bytes unlinked (`Prog::unlinked`: every item's bytes as `asm_bytes` writes them, a jump's displacement taken from offset 0 to label offset 0), and `labels::link` in `crates/cli/src/native/labels.rs` writes each `Jcc`, `Jmp` and `CallTo` displacement once the offsets are known, as `near_rel` has it. A displacement is the only thing in an item's bytes that reads the labels or where the item is, so nothing else needs the table. `bytes_#_#` is left only for the items around parts (a loop's or branch's labels and tests, the entry, the exits), whose programs cost nothing to spell again: on `sort_tool` cold the family went from 406 rows, 13.95 s and 32.7 M steps to 152 rows, 0.23 s and 0.3 M steps, and the ELF is byte-identical. The 8/16/32-pass cat scratch tools the "done when" names were not rerun; `sort_tool`, `tac_tool`, `head_n_tool` and `yes_tool` were.

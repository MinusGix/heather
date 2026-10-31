---
title: Read each part's bytes once instead of re-emitting it in the fork
status: open
labels: [native,performance]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-31
updated: 2026-10-31
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

---
title: Tighten the structured x86 lowering's code size
status: open
labels: [compiler,x86,native,perf]
created: 2026-09-29
updated: 2026-09-29
---

The structured x86 lowering emits code about three times larger than it
needs to be. Measured on `field_line` (docs/native-wc-design.md §5.1): a
restoring step or a mark is 68–84 bytes where about 20–30 would do, so
`field_low` is 1,911 bytes and `field_high` 2,792. What costs the bytes:

- a comparison materialises its bit (`movabs 0` into a register, `setb`,
  `mov`, `test`) and branches on the test, instead of branching on the
  flags the `cmp` set;
- a copy is `movabs 0; or` (13 bytes) instead of `mov` (3);
- every immediate is a 10-byte `movabs`, including zero and small weights;
- a doubling is `mov`/`add`/`mov` through RAX (9 bytes) rather than one
  `add r, r`, so `raise32` is 288 bytes.

Certificate cost follows the node count, so a tighter lowering also makes
certification cheaper (field_low 36 s, field_high 65 s at width one).

Not blocking: [[native-wc]] lifted the one-page program limit instead
(design §8.4). The fix is a set of new certified lowering shapes (flag
branches, register copies, sign-extended immediates, in-place two-operand
arithmetic), each with its own execution lemma.

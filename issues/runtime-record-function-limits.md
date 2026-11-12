---
title: A runtime fn of a laid record: what it does not take yet
status: open
labels: [native,runtime-fn,layout]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-12
updated: 2026-11-12
---

What a `runtime fn` of a laid record does not take yet (docs/layout-design.md §9.5, round 3; probes in `lib/_tests/native/runtime/runtime_held_tests.hthr`). Each is refused by name unless noted.

- **A branch that is not the function's last statement, with a store in an arm.** It elaborates to a branch inside `Mutated`, which the reflector refuses ("write the branch around the whole result, each arm its own end"). A tail `if`/`else` works.
- **A call of another function of the record** (`t.bump()` inside `Tally::twice`). The callee would be a writer lent the same span, and its marks the caller's.
- **Operands and results that are not 64-bit words.** A `u32` result, a `Nat` operand, a `Bool`.
- **A field whose codec has no accessor** (a `u16`, a `u8`, an array): it can sit in the record, and a function that neither reads nor changes it compiles. Arrays are round 4's.
- **Loops.** Round 4.
- A function that changes nothing is compiled as a function that writes its span (it stores nothing). Its code is right and it is marked as one that may leave the file changed, so a caller cannot yet learn the file is still from the mark.
- The refusal for a record that is not laid says "`Plain` has no runtime layout under the reflected fragment". It could say `laid record`.
- The generator's run is long for a long function: it grows with the square of the statements (each statement's reads go through every earlier store when the lowering is checked), outside the kernel as much as in it.

Found on the way and fixed in the same round: `laid record` stopped at fourteen fields (what it published grew with the cube of the fields and passed what the host reads of one reply; it now holds each shared term once), and the elaborator's reduction request walked a record updated field by field as a tree (fields to the power of updates; `contract_projections` now visits a shared node once).

Related: [[sha256-context-type]], [[layout-classes]], [[conversion-callee-unfolded-before-the-meet]], [[conversion-proof-compared-at-computed-type]].

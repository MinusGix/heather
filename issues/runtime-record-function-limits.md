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
- **A field whose codec has no accessor** (a `u16`, a `u8`, an array of them): it can sit in the record, and a function that neither reads nor changes it compiles.
- **An element of an array at an index that is not a literal.** An array of words is read and stored an element at a time at literal indexes (`vector_index(t.f, 3, trivial)`, `t.f := [a, b, …]`, `t.f := vector_update(t.f, 3, w)`; probes in `runtime_held_array_tests.hthr`). An index that is a word needs a reader marked with a family of parts and a bound the body's test gives, which is theory (`rt_held.hthr` keys a mark's fields by a literal offset).
- **The index spelled `t.f[i]`.** `v[i]` is the kernel's `nth` at a `Fin`, which the host's `View` shows no layer of, so the reflector answers "a form the reflected fragment does not have". It is `vector_index(v, i, trivial)` by `refl`. Either the view presents it or the reflector asks whether the term is an entry; and `t.f[i] := w` is not a place yet (a parser lowering to `t.f := vector_update(t.f, i, w)`). Both are surface, to settle with the index's type when it is a word.
- **A word array read as bytes.** `sha256_take_block` and `sha256_begin` store bytes where the schedule's and the working variables' words lie. At the record that is a second part over the same bytes (`[u8; 256]` over `[u32; 64]`), and a store through one changes what the other reads.
- **Loops.** Round 4.
- A function that changes nothing is compiled as a function that writes its span (it stores nothing). Its code is right and it is marked as one that may leave the file changed, so a caller cannot yet learn the file is still from the mark.
- The refusal for a record that is not laid says "`Plain` has no runtime layout under the reflected fragment". It could say `laid record`.
- The generator's run is long for a long function: it grows with the square of the statements (each statement's reads go through every earlier store when the lowering is checked), outside the kernel as much as in it.

Found on the way and fixed in the same round: `laid record` stopped at fourteen fields (what it published grew with the cube of the fields and passed what the host reads of one reply; it now holds each shared term once), and the elaborator's reduction request walked a record updated field by field as a tree (fields to the power of updates; `contract_projections` now visits a shared node once).

Related: [[sha256-context-type]], [[layout-classes]], [[conversion-callee-unfolded-before-the-meet]], [[conversion-proof-compared-at-computed-type]].

## Log

- 2026-11-12: Measured 2026-11-12: under the test profile's binary (the one the whole-library gate runs) the generator takes far longer than under the release binary on the same function, by a factor of tens (a nine-statement function a few seconds against most of a minute; a function of nine read-and-store statements past three minutes, which with the rest of its test file passed the gate's per-module CPU rail). The probes keep `State::init` and drop the longer cases for that reason. Where the factor comes from has not been looked at.
- 2026-11-12: 2026-11-12, PR #551: array fields, at literal indexes. A record function reads `vector_index(t.f, i, trivial)` and stores the entries of a field's new value that changed, each by the element codec's accessor where the element's part lies; the marks name only the elements the function reaches. compile-x86 exports a record function as its function over the span. `Sha256::init` is the first function of the context record that is linked (`sha256_init` is its code).

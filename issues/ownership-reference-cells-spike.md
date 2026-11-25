---
title: References held in memory down to x86: a shadow beside the bytes and an injection of blocks
status: open
labels: [ownership,native,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The third experiment of `docs/language/ownership-design.md` (§16, the riskiest package's earliest test): references held in memory, down to x86. §15.7 settles that a reference stays a reference to the machine, crossing by an injection of blocks; §16 proposes making that change additively, with a shadow beside the bytes. Whether that works is unknown until something small is proved through.

## Scope

A toy language at the bytes level, in its own module:

- **Values** are words and references (a block and an offset). **Memory** is blocks of bytes with a shadow: which eight-byte slots of which block hold a reference, and to what.
- **Operations**: store a word, load a word, store a reference into a slot, load a reference from a slot, load a byte through a reference.
- **Its meaning** is unchanged by renaming blocks (state and prove that: no operation observes a block's address).
- **A lowering to x86** and its theorem, by an **injection**: each block's bytes are at its address off the shadow, a shadowed slot holds its target's address, blocks are disjoint; the injection is preserved by a run. Cite what the machine side has: `Loan`, `Spans` (`lib/std/arch/x86_64/x86_64_lending.hthr`), `DataRegion::loan` and the span lemmas of `x86_64_byte_memory.hthr`.
- **One program**: store a reference in a slot, load it back, read a byte through it; compiled, with its theorem. Controls: a byte load of a shadowed slot is refused or owes a fact; two blocks placed overlapping break the injection (a `¬` theorem).

## What it must find out

1. **Is the shadow additive?** Does a memory with an empty shadow reduce to the bytes-only statements that exist, so existing theorems are the special case?
2. **Does the register invariant split by kind?** Read the central invariant of `lib/native/function_ir/function_ir_lower.hthr` and `function_ir_lower_calls.hthr` ("a register holds the valuation's word") and say, from what the toy's proof needed, what it becomes for a reference and how much of those two modules it would touch. This is a reading and a judgment, not a change to them.
3. **What `Loan` needs** to cover a block obtained after entry (a new span carved from a supply).
4. **What a byte copy of a record holding references needs** (a typed copy, or fragments).

## Done when

The toy's theorem is proved through to x86 for the one program, the controls are theorems or refusals, and the log answers the four questions with evidence.

## What it assumes from elsewhere

- **[[ownership-discipline-over-code]]** owns the design this tests. It changes nothing in `lib/native/function_ir` or `lib/std/arch/x86_64` beyond lemmas added under new names.

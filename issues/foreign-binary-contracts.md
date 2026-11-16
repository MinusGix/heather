---
title: Prove contracts of foreign machine code (linking and modelling binaries Heather did not compile)
status: open
labels: [native, x86, linking, analysis]
area: heather-in-heather
created: 2026-11-11
updated: 2026-11-11
milestone: [none]
---

Minus (2026-11-11): a speculative idea, not to be done soon. To link an
external program or shared library, or only to model another program,
Heather reads its machine code and uses the tactics, proofs and analyses it
already has for its own compiler to predict what the code does and prove
properties of it, such as that a callee respects the caller's memory and
does not write over its stack.

Survey and design sketch: `docs/surveys/foreign-binaries-survey.md`. In short:

- `MachineStep` is a semantics of bytes in memory and never mentions the
  compiler, so a contract for foreign bytes is an ordinary theorem today.
  The note's probe proves `Site::Returns` for a function assembled by GNU
  `as`.
- Reading a binary is untrusted: a disassembler proposes a `Prog` and
  `assemble(prog) = bytes` is checked by evaluation. The check goes through
  the encoder, because `decode_step_form` is complete only on emitted forms
  (it reads an LEA as a store).
- Properties form a ladder: closed and decodable, footprint (`Wrote`,
  `Kept`, `Lends`), total, system calls, function, leakage. "Does not write
  over my stack" is the footprint rung.
- A foreign function with a proved contract is a `Compile(f)` instance,
  entering programs through `Asm::Proved` or `Callee`.
- The gap is the instruction set: the modelled forms are about a third of
  the instructions of `libc`, `libz` and `cat`, and no whole function.

## Scope when picked up

The rounds F0 to F6 of the note's §9. F0 (a foreign import as an assumed
contract with axiom provenance, no machine-code reading) is the only part
with near-term use.

## What it assumes from elsewhere

- **[[named-abi-contracts]]** owns contract names. Assumed here: only that a
  name selects a clause list that can be required of a callee as well as
  promised by one.
- **[[runtime-extern-c-abi]]** owns the spelling of imports. Assumed here:
  only that an import can carry a contract and a required level.
- **[[native-library-exports-design]]** owns `Wrote` and `Lends`. Assumed
  here: only that they stay relational (a `Star` of stores; stability under
  it), so widening what one store may be changes one definition.
- **[[x86-64-machine-model]]** owns the model and its coverage ledger.
  Assumed here: only that an unmodelled instruction has no step.
- **[[dataflow-checked-fixpoints]]**, **[[word-abstract-domains]]**,
  **[[wp-obligation-tactic]]** and **[[wp-view-separating-product]]** own
  the analysis and automation the proofs would be found with.

## Open questions

The note's §12: whether the assumed foreign contract is the first-class
notion to build first, whether this is a horizon area of its own beside
`rust-in-heather`, and the policy for growing the model at this scale.

## Log

- 2026-11-11: Minus read the note. Two modes are wanted: an assumed
  contract (an axiom, as expected, wherever verification is out of reach)
  and active verification at link time, up to the abstraction the caller
  cares about (a sort is verified to return something sorted, not to be a
  particular sort), limited to what the automation can prove. The probe's
  proof is too verbose to be read by a person or comfortably by an AI: the
  statement needs an embedding (a named contract predicate, a declaration
  with `ensures`) and the proof a tactic. Missing integer instructions are
  not hard to add; SSE is troublesome and important. Code that calls back
  out needs whole-program analysis and is a separate, harder matter. Not
  for now, but calling and being called by outside functions will be
  wanted. Recorded in the note's §13.
- 2026-11-11 (later): Minus corrected two readings of the dictated message
  (SSE is wanted as a high-quality model regardless of this; the idea is
  wanted but not essential) and rejected a per-declaration `ensures`: a
  foreign library should be a namespace, since many proofs are wanted and
  a large library (SDL2, OpenSSL) needs a model relating many pieces of
  state and what its functions do to them. The note's §13.2 restates the
  unit as a component with a model (calls as a command container, an
  abstract world, theorems over it) and a per-function `refines` line
  that is assumed or checked, which is the shape the Linux model already
  has with its bridge assumed.

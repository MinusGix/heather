---
title: Define the canonical scoped x86-64 machine model
status: open
labels: [compiler,semantics,x86,design]
created: 2026-08-25
updated: 2026-08-25
---

Define Heather's one canonical x86-64 architectural step relation for the
compiler's emitted subset.  It is a specification object first: simpler ALU,
location, memory, and stack models prove into it, and typed assembly lowering
proves against it.  A fast simulator and byte encoder are executable views or
refinements, not alternate authorities.

The source/provenance and licence boundary are recorded in
`docs/x86-64-reference-materials.md`.  Intel and AMD manuals are normative;
ACL2 X86ISA and K are independent formal cross-checks; XED owns encoding and
resource metadata checks; Remill and Ghidra are pragmatic additional oracles.
Heather's rules are original statements of architectural facts, not copied or
translated third-party semantics.

Indicative bottom interface:

```text
step : FeatureSet -> Instruction -> MachineState -> Outcome -> Type
Outcome = Normal MachineState | Fault Exception
coverage : Instruction -> Supported | Unsupported CoverageReason
```

Architectural choice/undefined outputs live relationally inside `step` and
only at the affected locations.  A specified exception is an `Outcome`.  A
rule Heather has not implemented is `Unsupported`.  These are three different
facts and must remain different constructors/judgments.

## Initial scope

Long-mode, sequential, scalar user-level integer code: moves and extensions,
LEA, add/sub/neg/inc/dec/imul, boolean operations, shifts, compare/test,
conditional selection and branches, and basic stack/call forms.  Postpone
`DIV`/`IDIV`, strings, atomics, floating point, SIMD, privileged instructions,
interrupt delivery, page-table execution, and the concurrent memory model.

Omission is not erasure.  Every unsupported fault or environmental behavior
must appear in the coverage ledger together with the precondition used by the
normal-path rule.  For example, a simple load theorem assumes a permitted
access; it does not claim x86 memory is total.

## Acceptance for the first design/spike

- Fix the mode/feature scope and define the initial register, flag, RIP, and
  byte-memory state boundary, with architecture/environment data separated.
- Define typed instruction and operand forms independently of byte encoding.
- Define the step/outcome/coverage distinction and a per-instruction-form
  ledger schema covering operands, implicit resources, defined/preserved/
  undefined flags, faults, omissions, sources, and cross-check status.
- Carry one vertical scalar spike—preferably `MOV r64,r64` and
  `ADD r64,r64`—from generic arithmetic/location facts to the canonical state
  relation.  Include a deliberately undefined-flag control showing that only
  that flag is unconstrained.
- State the normal memory-access premise even if the first spike is
  register-only, so the later load/store rules cannot acquire a silent total
  memory assumption.
- Sketch the abstract-stack-to-memory/RSP representation theorem before adding
  `PUSH`/`POP`; do not add a separate stack field to canonical machine state.
- Define the typed-instruction/encoding seam and validate emitted forms against
  XED without making XED part of the trusted semantic base.
- Cross-check each spike rule against Intel, AMD when locally available, ACL2,
  and K; discrepancies are resolved conservatively and recorded rather than
  averaged.
- Record every missing generic API as an issue at its natural library owner.

## What it assumes from elsewhere

- **[[fixed-width-bitvectors]]** owns arithmetic, comparison, slicing,
  extension, carry/borrow, and overflow facts.  This issue owns only their
  placement into architectural state.
- **[[relational-semantics-refinement-kit]]** owns relational choice and finite
  refinement algebra.
- **[[state-location-and-frame-kit]]** owns state update and unchanged-location
  reasoning; this issue supplies x86 register aliases and partial-write rules.
- **[[byte-memory-access-model]]** owns sequential byte accesses and explicit
  access outcomes.
- **[[finite-trapping-stack]]** owns the abstract LIFO/capacity laws; this issue
  owns their representation by memory and RSP.
- **[[ir-simulate-design]]** owns the machine-independent structured IR and its
  deterministic `simulate`; this model is a downstream lowering target.
- **[[compile-typeclass-design]]** owns how a generated artifact and its
  correctness proof are packaged.
- **[[effects-direction]]** owns eventual external interaction and concurrency;
  neither is silently decided by the sequential first slice.

## Log

- 2026-08-25: Filed after assembling the gitignored reference cache and
  identifying the five reusable library foundations above.  The first spike is
  intentionally allowed to begin before all five land: discovering a missing
  theorem/API is part of their requirements, but any provisional local helper
  must be re-homed rather than becoming an x86-owned generic library.

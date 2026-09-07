---
title: Name ABI contracts and make unspecified behavior explicit
status: open
labels: [compiler,abi,semantics,proofs]
created: 2026-09-07
updated: 2026-09-07
---

## Scope

Make calling conventions reusable named Heather contracts, usable by certified
Heather code and explicitly assumed foreign boundaries. Begin with the current
internal convention and a precisely labeled System V AMD64 integer-signature
subset. A name selects a specification; it is not evidence that a body follows
it, and an incomplete subset must not advertise full System V ABI conformance.

## Acceptance

- Parameterize contracts by target/platform and supported signature/layout.
  Identify the normative ABI source and revision for external conventions.
- Represent preconditions, argument/result placement, preserved state,
  permitted clobbers, stack rules, and normal-return obligations. Distinguish
  guaranteed, explicitly unspecified, and unsupported/unmodeled behavior.
- Interpret permitted clobbers relationally: callers cannot rely on an old
  scratch value. Do not equate unspecified state with zero, invalid memory, or
  permission to violate an unrelated preservation guarantee.
- Audit state beyond integer registers (including direction/control state,
  vector/floating-point state), narrow-value excess bits, stack arguments and
  red-zone rules against the selected source. For each item, encode it, state
  an explicit environment assumption, or restrict the profile. Missing model
  coverage must not silently become an ABI permission to clobber.
- Keep ABI mechanics separate from function results, memory effects, and
  termination. Compose the named convention with a function-specific contract;
  the ABI alone does not specify what a C function writes through a pointer.
- Distinguish a checked implementation witness from an explicit foreign
  assumption. A foreign caller theorem must retain the assumption; symbol
  resolution or an ABI label cannot discharge it or introduce a global axiom.
- Include ABI identity and relevant parameters in interface/artifact matching;
  diagnose incompatible conventions and unsupported signatures. Preserve the
  distinction between function-call conventions and syscall conventions.
- Demonstrate equivalent ABI use by an internal certified body and a conditional
  foreign-call specification. Reject reliance on an unspecified scratch value
  and failure to preserve required state.

## Source to pin during implementation

The maintained System V AMD64 psABI sources and PDF build are published at
https://gitlab.com/x86-psABIs/x86-64-ABI . Record a concrete revision and relevant
sections when implementing the profile; a moving branch link is not its identity.
Names and library API spelling remain design choices.

## What it assumes from elsewhere

- [[x86-calls-stack-frames]] owns concrete CALL/RET behavior.
- [[x86-call-memory-footprints]] owns frame and protected-memory obligations.
- [[runtime-extern-c-abi]] owns actual foreign import/export adapters and C tests.
- [[runtime-compile-opt-in]] owns runtime eligibility and marker syntax.

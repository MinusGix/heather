---
title: Export checked FunctionIR x86 bytes as a callable native function
status: closed
labels: [compiler,x86,cli,codegen]
created: 2026-09-07
updated: 2026-09-21
---



## Scope

Expose the existing elaborated-source FunctionIR/x86 lowering as a native
export command. Emit a callable two-argument SysV function as literal-byte
assembly, check an explicit equality between those bytes and canonical
encoding, and link/run it using a manual C wrapper and external toolchain.

## Assumptions

- [[function-ir-x86-lowering-generator]] owns straight-line backend refinement.
- [[function-ir-x86-constants]] owns immediate selection and canonical layout.
- [[function-ir-x86-emitter-migration]] owns the structured emission boundary.

## Acceptance

- `heather compile-x86` checks elaborated source and generated proofs before
  publishing assembly and its companion certificate.
- The emitted literal body bytes are checked against canonical encoding;
  a corrupted encoding is rejected.
- Only SysV caller-saved registers are allocated, with an explicit unproved
  return shim. The proof boundary is documented without claiming ELF or ABI
  certification.
- A checked-in source and C wrapper build and execute a native binary;
  differential tests include wraparound and high-bit inputs.

See `examples/x86-native/README.md` for the invocation and current limits.

## Deferred boundary

[[bitvec-ofnat-large-literals]] owns the observed full-width literal conversion
fuel limit. The initial native example uses a small constant; native runtime
arguments still cover arbitrary u64 values. General graph-size proof costs
remain owned by [[function-ir-x86-proof-scaling]].
The packaging residue from compiling the proof-support source into the general
CLI binary is owned by [[decouple-native-support-from-cli-binary]].

## Log

- 2026-09-07: Implemented compile-x86 with elaborated-source lowering, exact literal-byte equality, bundled proof support, and a caller-saved SysV register assignment. The 22-byte mix body links through the manual C wrapper and passes 10005 native cases. Focused encoding checks cover all ten instruction forms and reject corrupted encodings. Full-suite verification is in progress; full-width literal conversion residue is owned by [[bitvec-ofnat-large-literals]].
- 2026-09-07: Validation complete for this scope: all x86 groups and both new native tests pass in the full suite; native execution passes 10005 cases. The full parallel run reported INCOMPLETE with 2453 passes and no assertion failures because mutual_recursion received SIGKILL; its isolated retry passed 13/13. This unrelated suite-reliability residue is owned by [[mutual-recursion-test-rail]].
- 2026-09-07: Direct standalone ELF generation is owned by [[x86-static-elf-executable]]; assembly export remains the FFI path.
- 2026-09-07: The deferred literal boundary is closed by
  [[bitvec-ofnat-large-literals]]; `examples/x86-native/mix.hthr` now adds
  the full-width asymmetric constant `0x0123456789ABCDEF`, so the exported
  immediate's eight bytes are all distinct and the native cases check the
  byte order as well as the arithmetic.

---
title: Lay out certified code fragments and resolve symbolic references
status: open
labels: [compiler,x86,proofs]
created: 2026-09-07
updated: 2026-09-07
---

## Scope

Own the small composition/layout layer for multiple certified code and eventual
data fragments. Resolve symbolic references directly into a final image without
requiring ELF relocatable objects or a conventional external linker as Heather's
internal composition model.

## Acceptance

- Represent fragment identity, alignment, entry/export symbols, and typed symbolic
  references explicitly. Define deterministic placement and relocation encoding.
- Reject overlap, overflow, unresolved/duplicate symbols, and out-of-range relative
  displacements; state supported relocation kinds and byte order.
- Connect placed bytes and resolved addresses to fragment certificates, including
  preservation under permitted relocation and the composition obligations.
- Exercise multiple function fragments and boundary/error cases; feed the laid-out
  result into the existing image certificate and native executable path.
- Leave object-file import, shared libraries, and dynamic relocation as separately
  scoped extensions. Do not duplicate the canonical execution semantics.

## What it assumes from elsewhere

- [[x86-calls-stack-frames]] owns CALL/RET and calling convention correctness.
- [[x86-64-conditional-branch-layout]] owns the existing local branch-layout work.
- [[elf64-structured-image]] owns final ELF serialization.
- [[prog-extension-lemma]] is related legacy IR work, not a requirement to translate
  the current FunctionIR pipeline back through that representation.

## Log

- 2026-09-07: The first call-executable producer lays out entry/leaf/wrapper fragments directly, checks symbolic rel32 bounds, and rejects duplicate/unresolved symbols and stack overlap. General alignment/export/data-fragment interfaces remain in scope; current profile fixes byte alignment and three fragments.
- 2026-09-07: The three-fragment customer now builds and runs a 334-byte final ELF. Its caller-to-leaf rel32 is negative, with a checked modular target proof; layout tests cover signed bounds, duplicate/unresolved symbols, and code/stack overlap. No external linker or relocatable object is used. General fragment alignment, exported interfaces, and data placement remain open.
- 2026-09-07: Reusable placed-function summaries now have a separate owner, [[x86-reusable-callee-certificates]]. This issue retains placement, symbol resolution, and relocation obligations.

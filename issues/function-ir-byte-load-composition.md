---
title: Compose checked byte loads with typed source bodies
status: closed
labels: [compiler,function-ir,x86]
created: 2026-09-20
updated: 2026-09-20
---

Add a shared normal-path MOVZX r64, byte [base] load contract with explicit
canonical-address and option-valued read-access premises. Bind exact canonical bytes,
normalized byte placement, unchanged memory/flags, and preserved registers.
Compose this step with typed source artifacts using explicit parameter/register
maps; no scanner-specific model or fixed-register proof family.

Exercise all register encodings (including SIB and zero-displacement forms),
arbitrary memory types and byte values, denied/wrong reads, incorrect encodings,
and frame/result claims. Native assembly execution should independently check
representative loaded-byte bodies. Keep instruction fetch and fault handling
outside the stated normal-path boundary.

This is the successful-read prefix under [[native-bounded-loop-certificates]],
using [[function-ir-typed-source-publication]]. Selecting the actual loop bounds
branch, converting Nat cursor arithmetic, and composing a bounded complete trace
remain with the loop issue. [[byte-memory-access-model]] owns the broader general
read/write memory layer; this slice makes no total-memory assumption.

## Log

- 2026-09-20: Implemented the general x86_64_data_read normal-path model and a
  ReadThenArtifact composition schema. ByteReadAccess returns Option<BitVec(8)>;
  normal execution requires Some(byte) at the actual pre-load base register and
  a low-canonical address. The canonical MOVZX plan handles all base/destination
  registers, SIB bases, and zero displacement for Rbp/R13. The combined artifact
  retains physical load/body execution, published bytes, memory, RIP, and frames.

  generate_elaborated_read_x86 feeds one typed byte parameter from that read and
  automatically transports other input placements into the unchanged shared body.
  The existing CLI encoder moved into the shared lowering layer for reuse; load
  publication checks literal emitted bytes against the model's canonical bytes.
  Focused kernel, refusal, assembler, and native execution validation is running.
- 2026-09-20: Focused validation passes all 3 tests. Kernel checks cover arbitrary memory
  and byte values, scalar bitwise and Boolean bodies, and a conditional body
  with payload/discriminator results. Every base/destination register pair
  (256 canonical encodings) agrees with both the model and the assembler.
  Native execution covers all 65,536 byte/input pairs for each of two clients
  (131,072 calls), reading the last byte before an inaccessible page and checking
  that memory is unchanged.

  Negative controls reject MOVSX substitution, missing SIB, wrong byte results,
  false register frames, denied reads, noncanonical addresses, and access evidence
  for the wrong address. The source adapter declines non-byte/missing parameters.
  The multi-result test supplies an additional legacy byte-addressable scratch
  register; the selector's register-pressure refusal remains unchanged.
  Plain full scripts/test is running, including existing native encoder/export
  regressions. No resource limits changed.
- 2026-09-20: The first full run completed all new byte-read checks and reported no assertion
  failures, but was INCOMPLETE because the older combined narrow-certificate
  binary hit its CPU rail. [[function-ir-narrow-certificate-test-margin]] now
  separates its existing primitive and complete-body checks into two processes,
  without changing assertions or limits. Both focused targets pass. Final plain
  full validation is rerunning on that tree.
- 2026-09-20: Completed and validated with plain scripts/test: 2863 passed, 0 failed, 5 ignored.
  The full run includes the new model/typed load-body artifacts, all 256 canonical
  register encodings, assembler agreement, 131,072 native page-boundary calls,
  negative access/encoding/frame controls, conditional multi-result composition,
  and existing native exports through the shared encoder. No limits changed.

  The normal successful-read prefix is complete. Actual loop bounds-branch
  selection, the Nat cursor/address relation, and complete bounded traces remain
  under [[native-bounded-loop-certificates]]. Fetch, faults, RET, and OS calling
  convention remain outside this adapter's certificate boundary.

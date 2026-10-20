---
title: Certify x86 calls and concrete stack frames
status: open
labels: [compiler,x86,proofs]
area: heather-in-heather
created: 2026-09-07
updated: 2026-09-19
---

## Scope

Own canonical CALL/RET execution and the lowering/certification of function calls
and concrete frames. Represent the stack through RSP and byte memory, including
return addresses; do not introduce an unrelated magical stack state.

## Acceptance

- Model the supported CALL/RET forms, instruction lengths, return-address push
  and pop, and explicit memory-access and stack-capacity preconditions.
- Specify argument/result placement, clobbers, preserved live values, frame
  layout, and alignment for the initial Heather calling convention.
- Compile and certify at least two functions with nested calls and returning
  results. Test return addresses, preservation, alignment, and failure conditions.
- Explain supported spills and locals; reject unsupported frame shapes clearly.
- Keep native convention choices distinct from C interoperability adapters.

## What it assumes from elsewhere

- [[x86-64-machine-model]] owns canonical machine semantics.
- [[byte-memory-access-model]] owns memory accesses; [[finite-trapping-stack]]
  owns the separate abstract bounded-stack representation problem.
- [[x86-symbolic-fragment-layout]] owns placement and relocation of code references.
- [[runtime-compile-opt-in]] owns eligibility of transitively demanded callees.
- [[runtime-extern-c-abi]] owns foreign convention boundaries.

## Log

- 2026-09-07: Implementing the first forwarding-wrapper/leaf executable milestone: actual nested near CALL rel32/RET, byte-addressed return slots, a dedicated RW ELF stack page, and a callee contract consumed by the caller result proof. The larger issue remains open for general source-call graphs, frame locals/spills, and exception outcomes.
- 2026-09-07: First executable milestone works: a checked 334-byte ELF runs entry -> forwarding caller -> arithmetic leaf -> caller -> entry and exits with the source-result byte 197. Near CALL/RET use byte-memory return slots, two aligned calls, an owned RW/NX page, and a restored final RSP. The leaf contract certifies result, return target, memory preservation, and RBX/RBP/R12-R15 preservation. Focused kernel controls reject invalid stack premises, mutated CALL/return bytes, and executable-stack flags; broader call graphs and locals/spills remain open.
- 2026-09-07: Final validation: full HEATHER_TEST_JOBS=3 scripts/test completed with 2489 passed, 0 failed, 5 ignored. The nested-call integration test built without a linker, checked the ELF/contract claims, and executed the result in 229.42 seconds under the ordinary 300-second CPU and 4 GiB limits. Direct execution and readelf/objdump inspection also confirmed the 334-byte image, backward CALL, two RETs, separate RX/RW mappings, and exit status 197.
- 2026-09-07: Follow-up ownership: x86-call-memory-footprints owns callee write permissions and caller protection; x86-caller-stack-locals owns the next executable customer; named-abi-contracts owns named convention policies; x86-reusable-callee-certificates owns compositional function summaries. See [[x86-call-memory-footprints]], [[x86-caller-stack-locals]], [[named-abi-contracts]], and [[x86-reusable-callee-certificates]]. The validated baseline implementation is still pending its implementation commit; review closure when it lands.
- 2026-09-19: Broader bounded source-call composition is owned by [[x86-source-call-composition]]; general call graphs, spills, and callable caller contracts remain here.
- 2026-09-19: Reusable summaries for composed callers are owned by [[x86-composed-caller-summary]], with [[x86-composed-caller-register-saves]] covering larger leaf register demands. The first summary retains a fixed incoming stack position; general frame relocation and call graphs remain follow-up scope here and in [[x86-call-memory-footprints]].
- 2026-09-19: Checked one-slot caller saves/restores are complete in [[x86-composed-caller-register-saves]]; [[x86-composed-caller-multi-slot-spills]] owns extension to multiple simultaneous slots and ABI save frames.
- 2026-09-19: Multiple simultaneously live caller save slots are now implemented by [[x86-composed-caller-multi-slot-spills]], using only scratch registers and liveness-sized aligned frames. General expression spilling, ABI-preserved register allocation with incoming-value saves, arbitrary incoming stack positions, and broader call graphs remain future scope here; the multi-slot milestone does not allocate ABI-preserved registers.

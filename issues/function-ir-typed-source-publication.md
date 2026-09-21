---
title: Publish typed source results through shared physical artifacts
status: closed
labels: [compiler,function-ir,x86]
created: 2026-09-20
updated: 2026-09-20
---

Connect typed structured source reflection to the shared physical result artifacts.
The public boundary should quantify source arguments (including erased unused Nat
parameters), require normalized register placements, and certify each output
against an observation of the actual source result. Internal valuations and graph
premises must not escape into the public contract.

Support scalar BitVec/Bool results and reflected two-constructor scalar choices
using explicit result placements. Reuse shared physical execution, layout,
decoding, memory, and register-frame certificates. Cover neutral inputs, arbitrary
memory types, constructor discrimination, payloads, and rejected mismatched
placements/source claims. The native CLI calling convention remains separate.

Builds on [[native-bounded-loop-certificates]]; the complete search_body is a
customer, not a special machine rule. Guarded reads and bounded-loop execution
remain subsequent work under that issue.

## Log

- 2026-09-20: Implemented generate_elaborated_typed_x86 over shared structured selection and
  certificates. The public contract quantifies typed source arguments and normalized
  placements; generated valuations close internal graph premises. Scalar and
  choice outputs receive source-named artifacts over the same execution. General
  Boolean-branch observation proofs preserve constructor identity and payloads.
  The complete search_body publication and separate scalar/choice examples check;
  consumer/negative controls and full validation are in progress. Native CLI ABI,
  guarded reads, and complete loop execution remain separate.
- 2026-09-20: Focused validation passes both publication targets. The complete search_body
  publishes payload/discriminator artifacts against the actual source call, with
  an arbitrary memory type and universally quantified unused Nat cursor. Separate
  checks cover neutral byte/one-bit/full-word inputs, zero-width constant output,
  and a distinct scalar choice type. A consumer uses the discriminator artifact;
  wrong result register, incorrect input placement, and swapped constructor
  encoding are rejected for type disagreement.

  An initial combined target exceeded the existing resource rail while duplicating
  the large search body's consumer checks. The complete search publication remains
  covered; consumer/rejection controls use the smaller independent choice and run
  in a separate target. Limits are unchanged. Plain full scripts/test is running.
- 2026-09-20: Completed and validated with plain scripts/test: 2860 passed, 0 failed, 5 ignored.
  Both new publication targets, existing physical certificates, and native
  regressions pass under unchanged resource limits. The typed public artifacts
  name the actual source call and require only source arguments plus normalized
  input placements. Scalar and choice interfaces, constructor identity, wrong
  register/input controls, and the complete search_body are covered.

  This closes certificate publication. The native CLI ABI remains two word inputs
  and one word result; guarded reads and complete bounded loops stay with
  [[native-bounded-loop-certificates]].

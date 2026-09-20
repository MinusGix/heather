---
title: Define source and FunctionIR contracts for bounded read-only buffer loops
status: open
labels: [compiler,function-ir,memory,design]
created: 2026-09-20
updated: 2026-09-20
---

## Scope

Define the smallest source-to-FunctionIR contract needed by the two clients in
[[native-shared-lowering-milestone]]. This is the source/IR design and semantics
step, before native loop selection. The removed scanner's ScanCode, register
assignments, status tags, and fixed 256-step wrapper are not compatibility
requirements.

## Acceptance

- Choose one explicit bounded source iteration/recursion fragment and reflect
  its elaborated body using resolved operation identities. Unsupported forms
  decline; a certificate names the actual source definition.
- Specify the source parameter/result interface and value representation for
  buffer, needle, cursor, and budget. Do not inherit the arithmetic frontend's
  two-argument restriction or the removed scanner's register ABI implicitly.
- Define the corresponding FunctionIR loop interface: typed carried values,
  guard, body, continue/exit results, and selected-path read dependencies.
- Make the budget a semantic input with an explicit exhaustion outcome and
  documented precedence relative to end-of-input and early exit.
- Model reads from caller-owned immutable bytes, with source identity, base,
  length, cursor, and explicit access premises. Empty/exhausted paths must not
  require a readable next byte. Do not silently treat all addresses as valid.
- State cursor bounds and the word/Nat counter relation needed by native
  lowering, including nonwrapping advancement and no decrement underflow.
- Show the IR represents both occurrence counting and first-match search,
  with different carried results and exits; no parser-specific constructors.
- Check source agreement and IR validity/semantics over open inputs, with
  controls for stale source, wrong carried bindings, unguarded reads, and
  incorrect budget/exit behavior under existing limits.

## Boundaries

No allocator, AST representation, parser combinators, arbitrary recursion,
writable-memory effect system, or x86 register layout is required here.
An application theorem about counting/search is distinct from compilation
preserving the bounded source program's behavior.

## What it assumes from elsewhere

- [[byte-memory-access-model]] owns general storage/access-policy semantics;
  this issue owns integrating the minimal read-only dependency into FunctionIR.
- [[function-ir-recursive-structured-lowering]] owns reusable branch composition.
- [[native-bounded-loop-certificates]] will own the native realization of the
  contract chosen here; it must not invent a separate source-loop semantics.
- [[native-shared-lowering-milestone]] owns the two-client integration check.

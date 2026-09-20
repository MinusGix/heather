---
title: Compile decimal runs over a byte-buffer cursor
status: open
labels: [compiler,x86,parsing,proofs]
created: 2026-09-19
updated: 2026-09-20
---

## Scope

Next vertical slice toward the showcase calculator after
[[x86-buffer-cursor-recognizer]]: compile a source-defined decimal parser that
consumes a runtime byte buffer using fixed storage, reports the consumed cursor,
and distinguishes malformed input from arithmetic overflow. One executable
must process different inputs supplied after compilation.

## Acceptance

- Read guarded bytes repeatedly through a checked loop or bounded recursion.
- Accumulate decimal values with an explicit machine-word overflow outcome;
  relate successful results to natural-number decimal interpretation.
- Exercise empty input, leading/non-digit termination, multiple digits,
  nonzero starting cursors, maximum representable values and overflow.
- Keep the parsing logic in compiled source, with the host limited to storage
  and I/O. Retain the existing source and machine-code certificate boundaries.
- Use ordinary proof and process limits and separate bounded acceptance targets.

## What it assumes from elsewhere

- [[x86-buffer-cursor-recognizer]] owns the initial checked byte access and
  single-character runtime recognizer.
- [[function-ir-recursive-structured-lowering]] owns nested structured backend
  composition; function recursion and loop support require their own treatment.
- [[parser-combinator-library]] owns parser sequencing, alternatives, and
  recursion semantics for later compilation of the showcase grammar.

## Log

- 2026-09-20: Implemented a reusable bounded scan model and experimental native scanner-body lowering. Ordinary source matches, scalar lets, unsigned comparisons, and word arithmetic compile into branches and arithmetic; decimal_step and count_spaces use the same loop. The scanner has success/no-digits/overflow/limit outcomes and a 256-step bound. Body/source refinement, arbitrary-state live-register/memory frame facts, pure-model bounded refinement and exact byte encodings are checked. The complete physical loop trace remains explicitly open in [[x86-buffer-scan-loop-refinement]]; a generic natural-number decimal interpretation theorem also remains open. This issue is deliberately not closed by runtime tests or the weaker body/model theorem.
- 2026-09-20: The compiled 411-byte decimal scanner produces `ok 123 3` for `123+4`, accepts UINT64_MAX, and stops before the overflowing digit for UINT64_MAX+1. A count-spaces body uses the same compiler/loop. Encoding proofs are composed from literal output chunks after a monolithic byte equality exceeded ordinary proof fuel. The first acceptance run exposed a stale mutation locator; the second showed a proposed parameter mutation hit a constant Stop branch and was therefore harmless. Controls now target the complete body interface, plus a live-cursor clobber and wrong initial accumulator. Runtime oracle/guard-page cases passed in both runs; final verification is pending.
- 2026-09-20: A live-cursor clobber control correctly failed its frame proof, but checking all downstream stale semantic proofs also exhausted fuel. The control now isolates the unchanged generated frame obligation over the corrupted instruction list. The generator emits frame obligations before body-result obligations, so the native publication gate rejects live-state corruption at that local boundary. No proof or process limits were increased.
- 2026-09-20: The final dedicated scanner target passed (1 passed, 0 failed). It covers 65,792 byte/position cases plus 10,000 deterministic oracle cases, examples at the u64 boundary, protected pages and resource exhaustion, the independent space-counting body, standalone certificate replay, six certificate mutations, bundled-model substitution, and bounded alias-expansion refusal. The plain full-suite rerun is still pending; the first full run's two failures were the now-fixed mutation boundary and test-binary re-exec race.
- 2026-09-20: Final plain scripts/test passed 2834 tests, 0 failed, 5 ignored (363 seconds runner wall time). The scanner target passed in the full suite as well as independently. The runnable artifact is target/decimal-demo/decimal; the build/run and exact proof-boundary guide is docs/x86-64-buffer-scan.md. Runtime/source-body/encoding work is complete for this experimental slice. The full machine-loop trace and generic natural-number decimal interpretation theorem remain open, so this parent milestone remains open.
- 2026-09-20: The scanner certificate now includes a physical guarded-entry trace for bounds/fuel checks and the byte load, with conditional read permission, preserved state, and concrete branch/body-entry RIP proofs. Full machine-loop composition and the natural-number decimal fold remain open in the existing scope; the CLI continues to label the export experimental.

---
title: Certifying arithmetic and bitvector proof automation
status: open
labels: [proofs,elaboration,metaprogramming,stdlib,ergonomics]
created: 2026-08-26
updated: 2026-08-26
---

The proof of executable carry correspondence is the right refinement theorem
and the wrong amount of hand-written ceremony. Its mathematical content is a
standard pattern: induct on bit width, expose one constructor layer of each
interpretation, split the three Boolean inputs, and normalize linear natural
arithmetic. The current library proof manually supplies the doubling lemmas,
sum permutation, threshold normalization, and all eight full-adder cases.

Build this as certifying automation outside the trusted kernel. The solver may
normalize semiring expressions, decide the Presburger fragment, split finite
Boolean cases, and use registered structural interpretation lemmas, but its
result is an ordinary proof term checked by the existing kernel. Failure must
return structured search state and the used lemma set in the style of
[[grind-port]], not merely `failed`.

The carry theorem is the first acceptance customer:

```text
carry_add_bit(n, a, b) = True
  iff
pow(2, n) <= toNat(n, a) + toNat(n, b)
```

Automation should synthesize essentially the currently landed induction and
finite case analysis without reducing `pow(2,64)` or expanding closed unary
numerals. A mutation of the majority function must be rejected. The generated
term should remain compact enough to check at open width under default fuel.

This issue explicitly does **not** authorize an elaborator heuristic that
silently rewrites arbitrary definitions such as `2 * n` into a preferred
recursive orientation. Such rewrites are performance-sensitive, hard to
predict, and can change which equations are definitional. Library definitions
should choose executable normal forms deliberately; automation proves their
extensional correspondence. A diagnostic or lint for forcing obviously huge
unary closed computations is compatible with that division.

## What it assumes from elsewhere

- **[[grind-port]]** owns the general certifying solver and structured failure
  interface. This issue owns the arithmetic/finite-domain component and its
  first bitvector customer.
- **[[bitvec-closed-reduction-cost]]** owns evaluator resource failure. Proof
  automation should avoid pathological reduction, not disguise a kernel crash.

## Log

- 2026-08-26: Filed from the executable carry proof. The direct 64-step
  Boolean control is cheap; the need for automation comes from proof
  construction and algebraic normalization, not from the semantic algorithm.
- 2026-08-26: Arena/cache measurements sharpen the first implementation
  milestone. A small certifying analyzer (`certgen` on `add`) uses only 1,498
  cached term values and never evicts, so "a Rust tactic necessarily emits a
  certificate the kernel cannot afford" is not supported; certificate SHAPE
  remains the variable to control. Start below the eventual tactic surface:
  a deterministic proof-term reconstructor for open Nat linear expressions,
  plus exhaustive Bool splitting, whose output uses named library lemmas and
  never evaluates closed `pow(2,n)`. Pin (1) the used-lemma list, (2) a
  structured unsupported/stuck result, (3) the carry step's eight cases, and
  (4) kernel-gate value metrics for the emitted open proof. Only after that
  compact certificate checks should it be wired into `grind`/surface solver
  selection. This keeps solver engineering outside the kernel and makes the
  feared certificate-checking cost an acceptance measurement rather than an
  assumption.

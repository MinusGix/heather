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
- 2026-08-26: The first certifying fragment was implemented
  (`docs/certifying-arithmetic-automation-design.md`): checking-only `arith`
  reifies open Nat equalities containing opaque atoms, `+`, and `twice`, then
  emits an ordinary proof from the Nat AC/congruence kit. Success exposes atom
  and swap counts plus the exact used-lemma list; failure exposes its kind,
  goal, both available normal forms, and detail. The executable carry sum is
  the acceptance customer, an altered coefficient is refused, `pow(2,n)`
  remains opaque, and a written `arith` binding wins over the form. Metrics
  caught the first semantically poor certificate shape: eagerly turning every
  `twice(a)` into `a+a` cost 162,246 term closures, 10.6x the handwritten
  carry normalization. Preferring coefficient-preserving `twice_add` and
  expanding only on retry brought that to 62,886 (4.1x), with no cache
  eviction; both the absolute and relative bounds are pinned. Still open for
  the next named slice: exhaustive Bool splitting plus the two structural
  order lemmas, then whole carry-step orchestration and general grind wiring.
- 2026-08-26: The bounded Boolean slice was implemented. After trying direct
  conversion and additive equality, `arith` splits up to three `Bool` locals
  into an ordinary generated match tree. Leaves try conversion, additive
  reconstruction, then deterministic applications of
  `twice_le_twice_iff`/`twice_le_succ_twice_iff`; candidate probes are
  transactional and independently kernel-checked before the chosen expression
  enters ordinary elaboration. Reports now pin split and branch counts as well
  as the deduplicated lemma set. Mutated majority logic is rejected, four-input
  nontrivial contexts hit the explicit bound, and conversion bypasses that
  bound when the Booleans are irrelevant. `std/bitvec`'s manual eight-case
  `carry_threshold` is now `arith`. Whole-path metrics, including rejected
  probes, are 41,285 term closures versus 20,941 handwritten, with zero
  eviction and absolute/relative regression rails. Remaining work is relevance
  filtering or a general finite-domain search layer, broader arithmetic, and
  eventual whole-step/`grind` orchestration.

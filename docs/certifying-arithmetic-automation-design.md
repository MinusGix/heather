# Certifying arithmetic automation

Heather's first arithmetic automation is an elaborator-side proof
reconstructor. It is not a kernel evaluator, an oracle, or a new proof term.
The checking-only expression `arith` reads its expected type, constructs an
ordinary Heather proof expression from named standard-library theorems, and
sends that expression through ordinary elaboration and the declaration's
ordinary kernel gate. Consequently a defect in the Rust implementation can
cause refusal or a bad certificate, but the bad certificate is still rejected
by the kernel.

## Implemented fragments

The additive grammar is deliberately small:

```text
atom ::= any completely respellable elaborated Nat term
expr ::= atom | expr + expr | twice(expr)
goal ::= expr = expr
```

Atoms are opaque kernel terms compared structurally. In particular,
`pow(2, n)` is not evaluated or expanded. Addition is flattened and
right-associated; equality is decided by coefficient-preserving permutation
of the atoms. Proof reconstruction uses only `nat::add_assoc`,
`nat::add_comm`, `nat::cong_nat`, `nat::twice_add`, and, when coefficient
expansion is actually required, `nat::twice_add_self`.

`twice` has two normalization routes. The preferred route preserves it as a
coefficient and distributes it over addition with `twice_add`. If those normal
forms differ, reconstruction retries with `twice(x) = x + x`. This ordering is
certificate-shape policy, not semantics: expanding first made the carry
customer's seven-atom certificate roughly 10.6 times the checking work of its
handwritten proof. Preserving coefficients reduces that to about 4.1 times,
with no value-cache eviction under the feature-gated metrics acceptance.

The carry-oriented layer wraps that reconstructor in bounded finite-domain
splitting. If direct conversion and additive equality reconstruction fail,
`arith` may split every `Bool` local in the context, up to an intentional
three-input limit. It builds an ordinary nested `match` expression and closes
each leaf, in order, by:

1. definitional equality;
2. additive equality reconstruction;
3. a deterministic search over `nat::twice_le_twice_iff` and
   `nat::twice_le_succ_twice_iff`, including a successor on the right.

Conversion runs before collecting Boolean locals, so irrelevant inputs cannot
make an already-reflexive goal exceed the split bound. The initial splitter
otherwise remains intentionally context-wide rather than trying to infer
variable relevance. General relevance analysis belongs in a later search
engine; the small hard bound prevents an accidental exponential certificate.

The match leaves use an elaborator-private marker containing a NUL byte. It
cannot be written by Heather source and introduces no declaration or kernel
term. Each structural candidate is elaborated transactionally on a cloned
elaborator and kernel-checked before selection; the selected expression is
then elaborated normally and passes the enclosing declaration's kernel gate.
The actual `std/bitvec` `carry_threshold` truth table is now a single `arith`.

## Audit and failure interface

Every successful reconstruction records an `ArithReport` containing the atom
count, adjacent-swap count, Boolean split count, checked branch count, and
exact used-lemma list. Reports are drained with
`Elaborator::take_arith_reports`; a declaration that later fails loses its
reports transactionally, as it loses warnings and pending derivations.

Failure is structured as `ArithFailure`: the failure kind, original goal,
both normal forms where available, and a detail. Current kinds distinguish an
unsupported goal, an unspellable term, unequal normal forms, and an internal
reconstruction failure. Diagnostics render that state rather than collapsing
it to `failed`.

`arith` follows Heather's ordinary bare-form shadowing rule. A local, alias,
declaration, or expected constructor named `arith` wins, so the form reserves
no keyword and cannot reinterpret an existing program.

The feature-gated carry acceptance measures the whole generated path,
including failed candidate probes: 41,285 term closures versus 20,941 for the
handwritten eight-case match, with zero cache eviction. The test pins an
absolute 50,000-closure ceiling and a relative three-times ceiling.

## Explicitly deferred

- inequalities and Presburger reasoning;
- Boolean relevance filtering, more than three inputs, and finite domains
  other than `Bool`;
- general order reasoning beyond the two structural doubling lemmas;
- induction or whole-theorem orchestration;
- integration into a general `grind` state;
- a reflected in-Heather certificate checker.

The outer width induction remains explicit. A natural next slice is to expose
the same deterministic reconstruction through a small solver/search interface,
then let real residual goals determine whether general linear arithmetic or
whole-proof orchestration is more valuable. The fragment should not silently
widen into reduction of closed powers or unary numerals.

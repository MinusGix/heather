# Certifying arithmetic automation (retired `arith` design)

> Historical design record. The specialized `arith` checking form was removed
> after kernel-certified Omega covered its affine arithmetic customers.
> Boolean enumeration is now the general `split_all; all_goals { ... }`
> composition described in `docs/goal-combinators.md`; the bitvector carry
> theorem uses its direct structural eight-case proof.

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
`nat::add_comm`, `nat::add_left_comm`, `nat::cong_nat`, `nat::twice_add`, and,
when coefficient expansion is actually required, `nat::twice_add_self`.

`twice` has two normalization routes. The preferred route preserves it as a
coefficient and distributes it over addition with `twice_add`. If those normal
forms differ, reconstruction retries with `twice(x) = x + x`. This ordering is
certificate-shape policy, not semantics: expanding first made the carry
customer's seven-atom certificate roughly 10.6 times the checking work of its
handwritten proof. Preserving coefficients reduced that to about 4.1 times.
Naming the standard right-associated `add_left_comm` law then replaced every
expanded adjacent-swap subtree with one checked lemma application, reducing
the carry-shaped certificate to 41,353 term closures, about 2.7 times its
handwritten proof, with no value-cache eviction.

The carry-oriented layer wraps that reconstructor in bounded finite-domain
splitting. If direct conversion and additive equality reconstruction fail,
`arith` may split every `Bool` local in the context, up to an intentional
three-input limit. It builds an ordinary nested `match` expression and closes
each leaf, in order, by:

1. definitional equality;
2. additive equality reconstruction;
3. direct reification of the `nat::twice_le_twice_iff` and
   `nat::twice_le_succ_twice_iff` goal shapes, including structural
   successors on the right;
4. a compatibility search over those same applications when a reducible
   alias hides the structural shape.

Conversion runs before collecting Boolean locals, so irrelevant inputs cannot
make an already-reflexive goal exceed the split bound. The initial splitter
otherwise remains intentionally context-wide rather than trying to infer
variable relevance. General relevance analysis belongs in a later search
engine; the small hard bound prevents an accidental exponential certificate.

The match leaves use an elaborator-private marker containing a NUL byte. It
cannot be written by Heather source and introduces no declaration or kernel
term. Direct order reification reads the lowered `Iff` record's two directions,
recognizes the two `Le` applications, and reduces only a bounded closed Nat
addend (at most four successors) while preserving neutral `twice` heads. It
then emits one ordinary lemma application. A reducible alias may fall back to
transactional candidate inference on a cloned elaborator; the audit reports
that route separately. Either selected expression is elaborated normally as
part of the completed proof and passes the enclosing declaration's kernel gate.
The actual `std/bitvec` `carry_threshold` truth table is now a single `arith`.

## Audit and failure interface

Every successful reconstruction records an `ArithReport` containing the atom
count, adjacent-swap count, Boolean split count, checked branch count, direct
order-reification count, fallback candidate-probe count, and exact used-lemma list. Reports are drained with
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

The feature-gated carry acceptance runs the whole generated path. Its evaluator
collector pins the emitted proof against the handwritten eight-case match;
`ArithReport::candidate_probes` separately accounts for the unprofiled search
conversions. Zero cache eviction is required.

## Cost anatomy

The evaluator counters measure value-machine regions, not all tactic wall
time. That distinction matters for the two fragments:

- The Boolean certificate and handwritten eight-case match now have identical
  evaluator counts: 20,941 term closures, 9,200 type closures, and 1,405
  arenas. Earlier counts were almost exactly double because every speculative
  leaf was kernel-checked separately before the finished match was checked.
  Search now infers candidate types and compares those types, while the final
  declaration gate remains the authority on the emitted proof.
- Before direct order reification, a representative debug run took roughly 24
  ms to find, elaborate, and check the Boolean certificate versus 9 ms for
  handwritten source; both final kernel gates took about 5 ms. With all eight
  leaves reified directly and zero candidate probes, a representative run is
  11.6 ms total: 6.0 ms search/elaboration and 5.6 ms final gate, versus 7.9
  ms total for handwritten (3.0 ms elaboration, 4.9 ms final gate). These
  milliseconds remain diagnostic; the pinned rail is eight direct
  reifications and zero fallback probes.
- Before `add_left_comm`, isolated additive measurements assigned 28,220 term
  closures to permutation, 14,261 to reassociation, and only 155 to
  `twice_add`. The named swap law reduced the permutation case to 9,529 and
  the full carry-shaped certificate from 62,886 to 41,353. Its remaining cost
  is dominated by reassociation and by composing normalization/permutation
  proof chains, not by arithmetic reduction or Rust-side normalization.

Wall-clock figures are diagnostic samples rather than regression assertions;
the deterministic event counts and candidate-probe count are the pinned rails.

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

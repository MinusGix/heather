# A relation proof inside an ordinary proof

The [showcase](showcase/relational_proof.hthr) uses `rel_cong(h)` in a normal
proof position. Read it as: **use this proof to justify the change inside the
surrounding expression**. The spelling is a small elaborator entry point, not
a commitment to a general tactic language.

For `merge_twice`, associativity exposes the repeated input. Idempotence then
removes it inside the surrounding merge:

```heather
A.rel_trans(
    merge(merge(state, incoming), incoming),
    merge(state, merge(incoming, incoming)), merge(state, incoming),
    A.assoc(state, incoming, incoming),
    rel_cong(A.idem(incoming)))
```

The user supplies the mathematical step, `A.idem(incoming)`. Heather reads its
elaborated type, sees which subterms it relates, and obtains the `Respects2`
and `Reflexive` parent dictionaries from the local `Mergeable` assumption.
There is no per-proof operation rule table or textual relation matching.
The library's `merge_twice` now uses this proof directly. Transitivity and its
intermediate expression remain explicit in this round.

## When something remains to prove

For a unary observer, the compatibility requirement is
`PreservesRelation(same, same, observe)`. An ordinary local certificate of that
type is enough. Without one, the CLI reports:

```text
?compatibility : PreservesRelation(same, same, observe)
```

The goal retains the original local context and can be discharged normally:

```heather
rel_cong(h)
on ?compatibility := supply(xs);
```

For a binary operation it requests the corresponding `Respects2` dictionary.
A fixed subexpression uses reflexivity evidence; without a suitable dictionary
or local proof it leaves `?fixed : same(value, value)`. Merely having identical
representations does not manufacture a relation proof. Ordinary goal naming
adds suffixes when several obligations need the same label.

Generated obligations retain a readable spelling of their original type, so a
preservation goal is shown by its named requirement rather than an expanded
function encoding. This diagnostic spelling is never used for checking.

These are local proof obligations. An unfinished declaration is not registered,
and an `on` proof must pass the same checking as any other proof.

## Reconstruction boundary

The frontend reads the supplied proof and expected goal as resolved core terms.
It compares endpoint trees structurally, keeping identical occurrences fixed
and replacing a differing pair only when it matches the witness endpoints.
Repeated and partial occurrences are supported. No symmetry or operation
unfolding is guessed to explain a mismatch.

It emits ordinary applications of the supplied proof, reflexivity, binary
compatibility, and unary preservation certificates. Private aliases carry the
already-resolved terms through ordinary expression elaboration; diagnostic
printing is never used as input syntax. The declaration still passes the kernel
gate. The older source driver remains available as an inspectable certificate
construction example.

This first native fragment uses the same resolved relation on a single
Type<0> carrier. Contexts are homogeneous unary/binary applications with a
256-node / depth-32 traversal bound. Dependent contexts, relation changes,
native identity goals, and calculation-chain syntax remain future work. A
user declaration or local binding named `rel_cong` retains ordinary meaning.

## Validation

Plain `furnace run -- scripts/test` passed on the final code: **2,348 passed,
0 failed, 5 ignored**, including all 33 setoid/generator/proof-position tests.
The final run took 390 seconds. The showcase passed an independent CLI check;
the CLI's missing-observer diagnostic was also inspected and shows the named
preservation requirement quoted above.

The controls cover repeated and partial occurrences, fixed-value obligations,
binary dictionary resumption, separate calls' goals, wrong relations and
unexplained changes, invalid resumption, bounded traversal, expected-type
checking, name shadowing, deterministic elaboration, and preservation of
computationally observable evidence. No kernel rules or axioms were added.

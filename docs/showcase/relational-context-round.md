# Building proofs for expression contexts

The next small slice after [manual Mergeable](manual-mergeable-round.md)
is a library of proof constructors in `std/relation_context`.
[The executable showcase](relational_contexts.hthr) builds a
compatibility proof for an ordinary function:

```heather
fn receive_repeated<A>(known, incoming: List<A>) → List<A> {
    known ++ (incoming ++ incoming)
}
```

For a user, its promise is: **replace the incoming list with another list
containing the same members, and the result still contains the same members.**
The implementation can retain duplicates and ordering. The theorem describes
what this particular observer treats as unchanged.

## How its certificate is assembled

1. The input variable preserves the input relation (`respectful_id`).
2. The fixed `known` list has its own membership-reflexivity proof. Together
   they produce the constant-context certificate (`respectful_const`).
3. Append's existing binary certificate combines the two occurrences of
   `incoming` (`preserves_relation_binary`).
4. Another application of that rule combines `known` with this result.

Once assembled, the certificate transports any supplied `SameMembers` proof
through the complete function. `receive_repeated_rewrite` uses the law
`incoming ++ incoming ≈ incoming`. Discovering that context automatically is
still future work; these are the ordinary proof terms a generator can emit.

The general application rule, `respectful_ap`, allows *both* the function and
its argument to depend on the input. Its left and right carriers can all differ.
The binary helper specializes this construction to one self-related operation,
with independently specified input, intermediate, and output relations.

## Two boundaries worth preserving

**Fixed does not imply self-related.** A strict order does not relate a value
to itself. A proof-relevant relation may require a particular witness. The
constant rule takes that evidence explicitly, and may even relate two different
constant values on different carriers. A generator working with an equivalence
dictionary can obtain the evidence from reflexivity. The shared rule needs no
such assumption.

These rules are sufficient constructions, not a complete decision procedure.
For example, an empty input relation makes preservation vacuous even if the
fixed outputs are unrelated. A missing constant-rule premise therefore leaves
room for a separately proved certificate for the whole context.

**Every observer needs its own certificate.** The showcase's `observe_received`
accepts precisely the preservation proof required to compose an observation
with this function. For raw list length, that proof cannot be supplied at
`SameMembers` and Nat identity: [the earlier showcase](mergeable.hthr)
already refutes it. A failed attempt to construct a certificate alone would
only establish that preservation has not been shown.

Duplicating the input also duplicates uses of the supplied relation proof.
These constructors do not equate those proofs or assume proof irrelevance.
No function extensionality, representative identity, or quotient axiom is used.

The constructors are transparent `fn`s. Heather makes `theorem` declarations
opaque: their stated preservation property would still be usable, but a client
could not reduce the constructed evidence to the supplied witness. The
Boolean-evidence test exposed this distinction and now checks that reduction
by `refl`. This is a reason to distinguish computational certificate
constructors from opaque law proofs when relations return `Type`.

The showcase supplies the existing named append and membership certificates
directly. The tested dictionary spellings `List::Mergeable<A>()` and
`List::Mergeable(...)` do not provide the desired
parameterized, indexed instance access here. Generic clients constrained by
`A: Mergeable(same, merge)` still resolve the List instance, as the preceding
round checks. Broader explicit dictionary-access syntax remains separate work.

## Syntax and the next generator

Existing `calc` syntax describes identity chains and desugars to `trans`.
Relational chaining and automatic context discovery are separate extensions;
this round changes neither parser nor elaborator. The explicit certificates
remain verbose and are intended as a generator's output vocabulary.

A bounded initial generator can target non-dependent application trees:
variables use identity, fixed terms request their relational evidence, and
applications combine certificates. Unsupported terms leave their exact
`Respectful` obligation. Relation choices must come from the requested contract
or operation certificate, rather than the raw carrier type. Recursion,
dependent application, certificate search, and relational `calc` remain with
their existing issues.

## Verification

`lib_setoid_mergeable` checks the showcase, heterogeneous application (Nat
related to List<Nat> by membership), differing fixed values, exact retention
of Boolean-valued relation evidence, and refusal to invent self-relatedness
for a fixed output at an empty relation.

Focused Furnace run: **7 passed, 0 failed**. Final plain
`furnace run -- scripts/test`: **2,322 passed, 0 failed, 5 ignored**
(419 seconds). Issue links and `git diff --check` also pass.

## Following round

[The bounded generator prototype](relational-generator-round.md) now exercises
these constructors from ordinary source and an explicit certificate table.
It includes missing-observer and invalid-observer controls; boxed-code and
meta-layer integration remain future work.

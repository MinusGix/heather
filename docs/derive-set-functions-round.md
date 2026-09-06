# Ask for a compatibility theorem for your function

The [author showcase](showcase/derive_set_functions.hthr) names an ordinary
function and asks Heather to prove that it preserves the selected relation:

```heather
fn augment<A, S>(union as ⊔: S → S → S, ops: SetOperations<S, A>, f: A → A, xs: S) → S {
    let mapped = ops.image(f, xs);
    xs ⊔ mapped
}

theorem augment_compatible<A, S: FiniteSets<A>(≈, ⊔, ops)>({ops: SetOperations<S, A>}, f: A → A):
    PreservesRelation(≈, ≈, λ xs => augment<A, S>(⊔, ops, f, xs))
{ rel_derive }
```

The function needs operations, so it takes operations without a law dictionary.
The theorem supplies the relation and laws. An earlier version made the
computational function carry the whole `FiniteSets` constraint; concrete proof
reuse then exhausted kernel conversion fuel. Keeping computation independent of
unused evidence avoids that repeated dictionary expansion.

The theorem declaration names the generated proof and states exactly which
relation it must preserve. The request does not register an instance or choose
a default relation. Its result is an ordinary checked theorem.

## How the proof is built

`rel_derive` introduces two inputs and evidence relating them. It examines the
resolved function applications in the conclusion, taking bounded transparent
reduction steps. Local bindings are handled by ordinary elaboration and
reduction. At each exposed application it first tries available compatibility
certificates, including fixed-argument operation-family laws such as image.
It composes those proofs using the existing relational congruence machinery.

`rel_derive(h)` is also available in a pointwise relation goal, using a supplied
input-relation proof. `rel_cong(h)` retains its existing behavior: it uses
certificates without unfolding named functions.

The showcase then binds `augment_compatible(f)` locally and uses `rel_cong`
inside a surrounding union. The named operation's body need not be repeated.
The [backend clients](showcase/derive_set_function_clients.hthr) consume the
same generated theorem at both lists and branching trees.

## A branch needs a mathematical fact

`relation_function::choose(condition, yes, no)` is an ordinary library
function. Its compatibility theorem requires equal Boolean choices and related
outputs in both branches. The generator recognizes its resolved declaration,
not an arbitrary function with the same spelling.

For a condition `test(xs)`, the sufficient requirement is:

```heather
PreservesRelation(≈, RelId<Bool>, test)
```

That says related inputs give the same Boolean result. A missing certificate
becomes a `branch_choice` obligation. Supplying a certificate in scope, or
returning one through an `on ?branch_choice := ...;` clause, completes the
ordinary proof. A fixed Boolean condition needs no observation law.

This is a sufficient proof strategy. A branch with identical outputs could
preserve the relation even when the condition does not; failure to prove equal
choices is not a counterexample. Arbitrary source `match`/`if` elimination is
not synthesized by this first implementation. The explicit `choose`
combinator gives the branch rule a small, independently checked meaning.

## Productive failures and limits

Missing operation certificates retain `compatibility` obligations. Unsupported
stuck definitions leave a pointwise `definition` obligation. Fixed values need
self-relation evidence. No relation is silently assumed reflexive, and missing
premises are not added to the theorem statement.

The search allows 512 visited nodes and depth 96, counting transparent
reduction steps. Separate requests retain independent obligation identities.

This is bounded derivation for homogeneous relations at `Type<0>`, not a
parametricity theorem for arbitrary programs. Recursive proofs, dependent
outputs, arbitrary branch synthesis, and mixed intermediate carrier relations
remain separate work. Generated proofs pass the normal elaborator and kernel;
no axiom or kernel reduction rule is added.

## Verification

The final plain Furnace suite passed: **2,418 passed, 0 failed, 5 ignored**.
Both showcase files also passed standalone CLI checking under a 4 GiB address
space limit and a 120-second CPU limit. Tests include both backends, missing
and incorrect branch evidence, resumed obligations, user-name shadowing,
ordinary missing-operation obligations, and independent goals from two requests
in one declaration. Existing relational congruence tests remain green.

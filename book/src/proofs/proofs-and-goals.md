# Proofs and goals

Proofs are ordinary expressions checked against proposition types. A theorem
body has the theorem statement as its expected type, so checking-only forms
such as `refl`, holes, anonymous constructors, and some tactics work there.

## Equality proofs

```heather
theorem same(n: Nat): n = n { refl }
```

`refl` proves definitional equality, not merely textual equality. Transparent
function reduction and the kernel's conversion rules may establish it.
Library theorems such as `sym`, `trans`, and congruence functions are ordinary
calls, not special tactic syntax.

Path induction is the built-in eliminator:

```text
j(proof, λ endpoint path => Motive, reflexive_case)
```

The proof fixes the left endpoint and family. The two-binder motive ranges
over the right endpoint and path.

`absurd(p)` proves the expected goal from an equality between distinct
constructors. `trivial` is the canonical proof of `True`. Both are
checking-position forms and give way to a user binding of the same name.

## Goal holes

Write `?name` or `?` to postpone a proof:

```heather
theorem example(n: Nat): P(n) {
    build(?side_condition)
    on ?side_condition := proof(n);
}
```

Goals live until the end of the declaration block and capture the local
context at their creation site, even inside a match arm. Discharge a goal by
name with `on ?name := expression;`.

An anonymous hole receives a stable generated name. Holes in argument
positions are normally named from the callee parameter, so diagnostics can
suggest the corresponding `on` statement.

Discharge every outstanding goal with a given proposition by statement:

```heather
on _: P := shared_proof;
```

The statement is checked separately in each captured context. Every matching
goal receives the proof; it is an error if no outstanding goal matches.

## Binding a goal as a value

An annotation creates the checking position needed by a hole:

```heather
let commuted: y = x = ?commutativity;
use(commuted)
on ?commutativity := commutativity_proof;
```

Without the annotation, a hole has no expected proposition and cannot infer a
type.

## Empty-block auto-reflection

At a checking position, `{}` tries `refl` once. If kernel conversion accepts
it, the block closes the goal. Otherwise it creates an ordinary open goal; it
does not search and does not make `refl` more permissive.

```heather
theorem computed(): add(2, 2) = 4 {}
```

## Axioms and trust

The checker tracks which declarations depend on explicit `axiom`s. Use
`heather axioms` to inspect provenance and `heather check --deny-axioms` to
turn dependencies on user axioms into a policy failure. Generated tactics
still produce ordinary terms that cross the same kernel gate.

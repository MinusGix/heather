# calc over `<=`, `<` and mixed relations

Date: 2026-10-15. Closes
[calc-over-order-relations](../issues/calc-over-order-relations.md), whose
trigger was hit by the rational order round
([rational-order-round](rational-order-round.md)): `two_halves_close` and
`Rat::dist_triangle` were inequality chains written as nested
`le_trans`/`le_respects` calls. The shape built is the one
[calc-equational-chains-design](calc-equational-chains-design.md) §4 pinned.

```heather
calc {
    (x -z).abs() <= (x -y).abs() + (y -z).abs() := x.dist_triangle(y, z),
    <= half + half := Rat::add_le_mono(hx, hz2),
    ≈ Rat::inv_succ(n) := Rat::inv_succ_half(n),
}
```

## The desugaring

A step is written with `=`, `≈`, `<=` or `<`. An all-`=` chain is unchanged
(right-nested `trans` with named endpoints). Any other chain folds right
through ordinary theorems in `lib/std/relation_props.hthr`, every endpoint
passed explicitly, so each written endpoint is checked, a single step's
included. Prepending step `i` to the rest of the chain picks its helper by
the pair (step relation, rest's relation):

| pair | helper | needs |
|---|---|---|
| `=`, `=` | `trans` | nothing |
| `=`, `R` | `relation_eq_l(R, …)` | nothing: transport along `=` |
| `R`, `=` | `relation_eq_r(R, …)` | nothing |
| `R`, `R` | `relation_step(R, …)` | `Transitive(R)` |
| `R`, `S` | `relation_trans(R, S, T, …)` | `Trans(R, S, T)` |

The chain's relation is the strongest it used, in `=` < `≈` < `<=` < `<`, and
the parser writes that result `T` itself, so instance resolution only looks
a pair up and never infers a relation. Relations are passed as operator
symbols, so `<=` at `Rat` is `Rat::Le` by its designation, exactly as `≈`
already was.

`Trans<A>(R, S, T)` is a three-relation class beside `Transitive`. The
same-relation case deliberately stays on `Transitive`: every carrier that
registers an order already has it (through `Preorder` or `LinearOrder`), and
a blanket `Trans(R, R, R)` from it would be a second route to the same
evidence.

## What is registered

- `Rat` (`rat.hthr`): `<=` with `<` either way round, and `≈` with either
  order either way round, over the existing mixed lemmas.
- `Nat` and `Int` (`order.hthr`, beside their `LinearOrder` instances):
  `Transitive` for `<`, and `<=` with `<` either way round.

A carrier or a pair not registered is a missing `Trans` instance at the
step, which is the negative control in the tests.

## Clients rewritten

`Rat::dist_triangle` and the lower bound of `Rat::abs_triangle` (both "rewrite
by `≈`, then `<=`"), and the showcase's `two_halves_close`, now read as the
textbook chain.

## Tests

`crates/syntax` pins the fold (pair helpers, the named result relation, the
`=` transports, and a missing relation token). `lib_std_rat.rs`
`order_calc_chains_mix_relations` checks homogeneous `<=`/`<` chains, mixed
`≈`/`<`/`<=` and `=` steps, `Nat` and `Int` mixed chains, and refuses: two
`<=` steps claiming `<`, a `<=` proof at a `<` step, a wrong single-step
endpoint, and a pair with no instance. `lib_setoid_mergeable.rs` turns its
old "mixed chains are refused" control into the new rule: `≈` beside `=`
checks, two unrelated local relations do not.

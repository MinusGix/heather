---
title: Indexed families at any index type, beside value parameters
status: open
labels: [inductives,indexed-families,elaboration]
area: language
created: 2026-11-09
updated: 2026-11-09
---

An inductive family can be indexed only by `Nat` or by a previously declared,
unparameterized, unindexed inductive (`index_type` in
`crates/elab/src/inductive.rs`). That restriction is route 1's and fording's:
both build the family by recursion on the index type. The `IWf` route does
not need it; its design note says so (docs/iwf-former-design.md §8.2: "`I`
may be any type … parameterized index types are fine. Only inversion (§8.3)
needs structure on `I`"). The elaborator still applies route 1's check before
choosing a route.

The inductive cover of a formal topology ([[inductive-formal-covers]]) needs
the general form:

```heather
inductive Cover<P>(le_p: P → P → Type, C: P → Type, ax: (a: P) → C(a) → Opens<P>, u: Opens<P>) : (a: P) → Type {
    Here(a: P, h: u.has(a))                                          : Cover<P>(le_p, C, ax, u)(a),
    Down(a, b: P, h: le_p(a, b), c: Cover<P>(le_p, C, ax, u)(b))     : Cover<P>(le_p, C, ax, u)(a),
    Axiom(a: P, k: C(a), f: (e: Exists<P>(ax(a, k).has)) → Cover<P>(le_p, C, ax, u)(e.witness))
                                                                     : Cover<P>(le_p, C, ax, u)(a),
}
```

Three refusals stand in the way, each a check that predates the `IWf` route:

1. **The index type.** `P`, a type parameter, is "unknown index type `P`".
   Wanted: any type, read under the declaration's type (and value)
   parameters, on the `IWf` route. Inversion at a constructor-headed index is
   then available only where `I` is `Nat` or a declared inductive, and a
   `match` at any other index is at a variable index, or abstracted
   (§8.3's tiers 1 and 2).
2. **Value parameters beside an index.** "`Cover` has both value parameters
   and an index: the two do not combine this round"
   (docs/surface-value-parameters.md §6). Wanted: value parameters substituted
   into the payload, the children's family and the index type, as on an
   unindexed declaration.
3. **Bare-variable results.** When every constructor's result index is a bare
   variable, the declaration is told that its index is a parameter
   (`all_bare_var_indices`). That holds only when the children sit at the
   same variable. An accessibility-shaped family (children at other indices:
   `b`, `e.witness`) is a genuine index, which `IWf` generates.

Also met by an infinitary field (`f: (e: …) → Cover<…>(…)(e.witness)`): with
value parameters, the uniform occurrence `D<p̄>(v̄)(e)` is not recognised by
the infinitary classifier ("a function whose result mentions `Cover` under
another type").

---
title: Add role-bearing aliases for classes
status: open
labels: [design,traits,elaboration,ergonomics,stdlib]
created: 2026-08-09
updated: 2026-08-09
---

Long-range design direction from the operation-indexed library discussion.
Many domains use the same mathematical structure several times on one carrier,
but the **role name** remains useful information:

```heather
alias class RefinementOrder<A> = Preorder<A>(refines as ⊑)
alias class PreferenceOrder<A> = Preorder<A>(prefers as ≽)
```

`RefinementOrder<A>` and `PreferenceOrder<A>` are not wrapper records and do
not create new kernel types. Both elaborate to an ordinary
`Preorder<A>(relation)`, so every theorem, projection, upcast, and dictionary
term for `Preorder` works unchanged. The alias adds an elaborator-visible
**role**: conventional parameter names and notation, a place for defaults,
better diagnostics, and a deterministic preference for an instance declared
under that alias.

This serves the common large-module spelling:

```heather
theorem refinement_preserves_preference<
    A: RefinementOrder + PreferenceOrder
>(...): ...
```

without recreating Lean-style parallel structure hierarchies merely to attach
the words "refinement" and "preference" to two preorders.

## Semantic boundary

An alias class is **transparent after elaboration**:

- its constraint lowers to the target class with the alias's parameter/index
  arguments;
- it has no fields of its own and no independent inheritance graph;
- an alias dictionary is the target dictionary, not a wrapper around it;
- an alias theorem can be used where the target class is requested with no
  cast or synthesized parent;
- the kernel and cache need no alias concept in checked terms.

It is **not erased before resolution and diagnostics**. The request remembers
that the user wrote `PreferenceOrder`, and an instance declaration remembers
that it was advertised under that role. Pretty-printing and error data preserve
the written alias even while exposing the lowered target goal when useful.

## Alias-preferred resolution: a named tie-break only

A request written through an alias may prefer the unique applicable instance
declared under that same alias. If none applies, resolution falls through to
the ordinary target-class rules. Strawman:

```heather
instance PreferenceOrder<Lottery>(agent_prefers) { ... }
instance RefinementOrder<Lottery>(information_refines) { ... }
```

Then `A: PreferenceOrder` may fill its relation slot with `agent_prefers`,
while a bare `A: Preorder` does not prefer either instance.

This must remain narrower than general instance priority:

1. the source explicitly names the role that activates the preference;
2. at most one alias-preferred answer may exist for an alias's resolution key
   (overlap is a declaration error, not declaration-order choice);
3. exact local/scoped evidence retains the ordinary resolver's precedence;
4. falling back loses the preference completely and runs the target class's
   normal deterministic resolver;
5. the result is kernel-checked at the transparent target type.

The alias name therefore nominates a structure only inside a request that
spells that semantic role. It does not make `agent_prefers` "the preorder on
Lottery" globally and does not change an existing bare `Preorder` request.

## Defaults and override

An alias is a natural home for defaults at three distinct layers, which the
design must not conflate:

- **presentation defaults**: parameter names and symbols (`prefers`, `≽`);
- **resolution defaults**: the alias-preferred instance above;
- **field defaults**: omitted fields when constructing the underlying class,
  owned by the ordinary class-default mechanism rather than redefined here.

All presentation choices must remain overridable at the use:

```heather
A: PreferenceOrder(pareto_prefers)
A: PreferenceOrder(pareto_prefers as ≽)
```

The exact syntax is open. Supplying an explicit relation must suppress the
alias's resolution preference: the user has already identified the structure.
Supplying a symbol override changes presentation, not the underlying role or
instance key.

## Diagnostics

Failure data should name both views:

```text
could not resolve PreferenceOrder<Lottery>
underlying goal: Preorder<Lottery>(?prefers)

alias-preferred candidates: none
ordinary Preorder candidates:
  risk_dominates
  information_refines
  agent_prefers
```

Likewise, an alias-preference overlap names the alias, carrier/key, both
declarations, and their underlying indices. This is one of the feature's main
payoffs: a domain name survives long enough to explain why a structurally
ordinary `Preorder` was requested.

## Design questions this issue owns

1. Declaration and use syntax, including explicit index and symbol override.
2. The exact position of alias preference relative to local/scoped evidence
   and registry lookup, preserving the resolver's existing scope discipline.
3. The alias-instance uniqueness key for generic carriers.
4. Whether aliases of aliases are normalized transitively or refused in v1.
5. Whether a target-class instance may be advertised under an alias after its
   declaration, and how scoped installation interacts with the role.
6. Which alias metadata survives in interfaces/caches so separate modules get
   the same resolution and diagnostics.
7. How class inheritance shares presentation defaults without turning aliases
   into a second inheritance hierarchy.

## What it assumes from elsewhere

- **[[operation-indexed-classes]]** owns indexed class identity and the
  no-unpinned-choice rule. This issue adds one explicitly named role tie-break;
  it does not add general priorities.
- **[[class-default-operators]]** owns default notation advertised by an
  ordinary class. Alias-specific presentation may reuse that installation
  mechanism but may override its advertised symbols.
- **[[binder-symbol-as-notation]]** owns local symbol aliases for named
  binders. Assumed here: alias defaults ultimately install the same kind of
  local binding.
- **[[scoped-instance-installation]]** owns explicit scope overrides, which
  remain stronger than registry-level alias preference.

## Log

- 2026-08-09: Filed from the multiple-orders discussion. Decision direction:
  an alias is kernel-transparent but elaborator-visible; it names a semantic
  role, preserves that name for diagnostics, and may prefer the unique
  alias-named instance when the request itself uses the alias. It is a named
  tie-break only, not a general priority system.

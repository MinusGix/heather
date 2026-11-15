---
title: Free theorems for functions generic in an effect carrier, proved in the language
status: open
labels: [effects,relations,proofs,design]
area: tactics
milestone: [nh-effects]
created: 2026-11-08
updated: 2026-11-08
---

Minus (2026-11-08, on `docs/language/effects-locality-design.md` §5.6): a function
written against a small interface (`fn f<C>(c: C, d: Stdout<C> := infer)`)
should come with a *proof* that it treats its carrier only through the
interface, obtainable within the language. Today that holds only as a
metatheoretic intuition, and not even for every definition: code at layer
m can observe code, which is why [[certified-parametricity]] treats free
theorems as per-function certificates.

This is that issue's first concrete customer, at the shape effect
interfaces need, which is narrower than general parametricity: one type
parameter `C`, class dictionaries over it, `mut self` threading
(`Mutated<C, R>`), loops in `Partial`.

## Scope

- The statement. For carriers `A`, `B`, a relation `R: A → B → Type` and
  dictionaries `da: K<A>`, `db: K<B>` that are a simulation (each member
  takes `R`-related carriers and equal arguments to `R`-related carriers
  and equal answers), `f` at `A` and at `B` takes `R`-related carriers to
  `R`-related results (in `Partial`, up to `Eutt` with a relation on
  results). Stated once as `Parametric1(K, f)` in the library.
- The producer. A generator (a declaration-prefix one, or derived on
  request) that proves `Parametric1(K, f)` for `f`'s body by the
  relational derivation kit, refusing with a located reason at a step
  that observes code or uses an instance not built from `K`.
- Consumers, in this order: (1) a theorem proved at a pure carrier moved to
  `Io` (the note's `greet`: its call list at `Io` read off its pure run);
  (2) the footprint: `Io::Only(P, f)` at the `Io` instance from the
  instance's own footprint, for every `f` with `Parametric1`
  ([[io-footprint-facts]]).
- A negative control: a body that inspects code is refused, and the
  refusal names the step.

## What it assumes from elsewhere

- **[[certified-parametricity]]** owns per-function parametricity in
  general. Assumed here: only that a carrier-shaped fragment is a fair
  first slice of it.
- **[[effect-interfaces-over-carriers]]** owns the interfaces.
- **[[relational-transfer-core]]** owns the respectful relator this
  states the simulation with.

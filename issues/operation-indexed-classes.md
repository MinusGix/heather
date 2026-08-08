---
title: Operation-indexed classes: Monoid<A>(op) — the structure names its operation
status: open
labels: [frontend,elaboration,design,traits,stdlib]
created: 2026-08-07
updated: 2026-08-08
---

User insight 2026-08-07, from the add-vs-mul coherence discussion: 'kinda makes me think Monoid<R> is really Monoid<R, Op>'. The repo's own precedent is [[compile-typeclass-design]]'s `record CompileNat2(f: Nat -> Nat -> Nat)` (lib/ir_v1.hthr:1146) — a class ABOUT a value carries that value as a parameter, so 'which f is this an instance for' is kernel-checked. Applied to algebra: `class Monoid<A>(op: A -> A -> A) { unit: A, assoc: …, … }` — the operation moves from field to index; only unit and the proofs remain fields.

**What it dissolves**: the two-monoids-on-one-carrier problem, structurally. `Monoid<Nat>(add)` and `Monoid<Nat>(mul)` are DIFFERENT types — both register, no coherence conflict, no Lean-style hierarchy duplication, no to_additive. A lemma `requires Monoid<A>(op)` is proved once and spent at both. In `(a + b) * c` both structures are live and the op in the goal is the disambiguator — which is exactly how the operators round will want notation to link to theory. It also largely answers the explicit-projection skepticism (user, same date): a Ring-level lemma names its op in the goal rather than navigating a dictionary path (`r.mul_monoid.assoc`), so the low-level projection reasoning mostly never surfaces.

**What it costs**: (1) A consumer that today says 'give me THE monoid' (`mconcat<A> requires Monoid<A>`) becomes `mconcat<A>(op) requires Monoid<A>(op)` — a goal `Monoid<Nat>(?op)` is ambiguous BY DESIGN (add and mul both answer), so op must arrive from the caller, an argument or a default. This is the modes question wearing algebra clothes: op wants to be an INPUT position. (2) The (class, carrier-head) registry key cannot hold two instances at one head — value indices need the key extended by a spellable op name (a named-value discipline: the index must be a global reference, not an arbitrary term?) or the full-key work. (3) Resolution keying on a VALUE up to conversion — which layer 2's trial-based selection (build + kernel-check) already does by construction; the trial route is accidentally future-proof here.

**The likely synthesis, not yet decided**: two class styles for two directions of information flow, both over the same record substrate — indexed `Monoid<A>(op)` for theory (no coherence problem, op flows IN), and bundled/canonical classes (today's `Monoid<A>`, or a thin wrapper with a dependent field pair) for 'the default structure' consumers where the registry's coherence policy is the point. Lean has the same split (bundled Monoid vs Std.Associative-style predicate classes); ours can be honest about it because dictionaries are ordinary values and record value-parameters already exist.

## What it assumes from elsewhere
- **[[traits]]** owns the class/instance forms and the resolver. Assumed: classes gain value parameters the way records already have them; overlap/keying extends to value indices.
- **[[compile-typeclass-design]]** owns the CompileNat2 precedent. Assumed: only that the pattern stays 'index by the value the class is about'.
- **Modes** (traits layer-2 residue) own the input/output discipline this makes load-bearing.

## When
A design pass before the operators round would be ideal — operators want to know whether `Add` feeds bundled or indexed structure. Not scheduled.

## Log

- 2026-08-08: Boundary recorded by the type-projection round (docs/traits-type-projection-design.md §6), not decided: T.f at a value-indexed class would build C<T>(?op) — a meta in a value slot, ambiguous by design — so it is the same shape as the multi-parameter narrowing and should be REFUSED BY NAME when value indices land; the params.len()==1 filter gains a value-index test and inherits that diagnostic. Nothing in the projection design assumes one parameter in general. Also relevant when this designs: T::C takes no arguments, so an indexed class has no short dictionary spelling either (noted on [[traits]]).

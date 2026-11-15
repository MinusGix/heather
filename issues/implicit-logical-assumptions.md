---
title: "Assumption scopes and profiles: generalize first, discharge explicitly"
status: open
labels: [frontend,syntax,elaboration,traits,logic,proofs,design,ergonomics,tooling]
area: language
milestone: [math-specific-choice]
created: 2026-08-24
updated: 2026-10-26
---

Make a hypothetical logical context almost as comfortable as an ambient
axiom without confusing the two. A declaration should state the weakest
premise it needs, a block should be able to generalize all of its declarations
over a shared premise or named profile, and a caller should be able to supply
one concrete provider for that context. An `axiom` remains separate: it is a
named, irreducible trust leaf used only when somebody deliberately closes a
conditional world.

The earlier sketch in `docs/implicit-logical-assumptions-design.md` proposed
an axiom-specific fallback for selected `:= infer` parameters. This issue
supersedes that part of the sketch: there is only `infer`. Axioms are never an
ambient candidate set merely because they are visible or imported. Evidence
enters inference scope through an ordinary local/assumed value, a generalized
profile, or an explicit `using` scope.

The computational boundary from the earlier sketch remains: classical
excluded middle is opaque and cannot implement Heather's reducing
`Decide<P>` contract. Logical evidence and a decision procedure remain
different capabilities.

## The four operations

### 1. An exact requirement

The portable theorem asks for the narrowest proposition it actually uses:

```hthr
theorem choose<P>(
    hp: Or<P, Not(P)> := infer
): Or<P, Not(P)> {
    hp
}
```

`hp` is an ordinary implicit kernel Pi binder. At a call, `infer` first uses
an exact local or specialized constructive proof. Neither the declaration nor
the solver says anything about axioms or classical logic.

### 2. `assuming`: generalize a lexical item group

A shared hypothetical context is a block annotation which prepends an
ordinary implicit solver parameter to every declaration in the block:

```hthr
assuming hp: P {
    theorem recover(): P {
        hp
    }

    theorem harmless(n: Nat): n = n {
        refl
    }
}
```

The declarations elaborate as if written:

```hthr
theorem recover(hp: P := infer): P { hp }
theorem harmless(hp: P := infer, n: Nat): n = n { refl }
```

The parameter is added to **every** declaration, including `harmless`.
Whether the public type changes must be a function of the written block
boundary, never an inference over proof bodies. Calls among declarations in
the block pass the parameter through ordinary `infer`.

`assuming classical: Classical { ... }` is the named-profile form of the same
generalization operation. It introduces a binder; it does not mint a constant
and does not add axiom provenance. `assuming` is deliberately an **item-group**
construct: one declaration writes its ordinary `p: P := infer`, named
`requires p: C<A>`, or anonymous `requires C<A>` parameter directly. The new
syntax earns its place only by amortizing one telescope over several items.

A future namespace block may accept the same annotation without changing its
semantics. A whole-file form after imports may annotate the file's implicit
top-level item block. File scope is allowed because users will want it, but it
does not flow through imports and tooling should keep the resulting broad
interface visible.

Named and anonymous assumptions are comma-separated and share the requirement
grammar:

```hthr
assuming classical: Classical, Extensional { ... }
```

The anonymous value receives a hygienic, unwritable internal name and remains
available to resolution by type. The same anonymous spelling is useful for
ordinary class requirements (`requires Monoid<A>`); a name is written only
when the body needs to refer to the dictionary value itself. Section-level
type parameters are wanted eventually, but are not part of the first slice:
`ClassicalOn<A>` stays declaration-local until a group can bind `A` honestly.

### 3. Profiles: name a reusable assumption interface

One proposition needs no bundle. A reusable polymorphic world does. In
schematic syntax:

```hthr
profile Classical {
    em<P>(): Or<P, Not(P)>;
}
```

A profile is a named assumption interface and inference-provider set. Its
kernel representation may naturally be a record value; that representation
is subordinate to the surface invariant that it is an ordinary parameter and
can be implemented constructively, specialized, or axiomatically.

Inside

```hthr
assuming classical: Classical {
    theorem general<P>(): Or<P, Not(P)> {
        choose()
    }
}
```

the profile's `em` provider may discharge `choose`'s exact proposition. An
exact local `Or<P, Not(P)>` still wins. This lets a theorem ask for the narrow
premise when it can, lets another theorem specifically advertise a broad
`Classical` requirement when that is its honest interface, and lets a user
put a whole region in the classical style without repeating either spelling.

Profiles should be composable and may be narrower than one monolithic
`Classical`: excluded middle, choice, and extensionality are not forced into
one indivisible foundation. A broad convenience profile may still exist for
users who deliberately want the entire classical world.

### Library rule: exact proposition, then typeclass, then profile

Library APIs should prefer, in order:

1. the exact proposition or witness the theorem consumes;
2. a named, reusable typeclass capability indexed by the relevant type,
   proposition, value, or structure;
3. a broad profile such as `Classical` when the theorem genuinely ranges over
   many such capabilities or concision is the deliberate choice.

Examples of the middle layer are `DecidableEq<A>`, `Stable<P>`,
`HasUpperBound(xs)`, `Located(xs)`, `ChoiceOn<A>`, or a similarly precise
mathematical interface. A finite, discrete, bounded, or otherwise special
customer may implement one constructively. `Classical` is then a common
source of these narrower capabilities, not a label permanently attached to
their consumers.

Do not mark a profile intrinsically “nonconstructive” merely because its
general implementation is classical. `ClassicalOn<A>` may be constructively
inhabited for a special `A`; trust and reduction properties belong to the
selected provider. If editor ranking later needs author metadata beyond the
actual requirement and provider state, add it only from measured examples.

One narrow theorem is preferable to a mechanically duplicated
`foo_classical` wrapper when the broad profile merely discharges its solver
parameters. Duplication is nevertheless legitimate when the constructive
statement has materially different precision bounds, witnesses, or API shape
and the classical result is a useful general corollary rather than the same
call with one inferred argument. The wrapper should derive the constructive
theorem's exact premises and call it, keeping the relationship explicit.

### 4. `using`: supply a concrete provider

`using value { ... }` activates an ordinary value or profile implementation
for inference in one lexical block. It adds no parameter:

```hthr
using constructive_classical {
    theorem result<P>(): Or<P, Not(P)> {
        choose()
    }
}
```

The concrete provider may itself be proved, constructed, imported, or an
explicit axiom. Selection remains use-sensitive: entering a `using` block
creates no dependency by itself, and each committed declaration records only
the globals its elaborated body actually selected.

`assuming` and `using` therefore have deliberately different meanings:

- `assuming` introduces and automatically threads a requirement;
- `using` supplies a concrete implementation of a requirement;
- `axiom` creates a concrete implementation without proof.

## What an axiom is for

Within the pure logic, an axiom is never necessary. These contain the same
logical dependency:

```text
axiom a : A; theorem result() : T { ...a... }
theorem result(a : A := infer) : T { ...a... }
```

The first merely stops propagating `A` through interfaces and admits it as a
named fact of the trusted global context. The second exposes the condition.
A classical mathematics library may stay generalized over `Classical`
forever and need no classical axiom at all.

The genuine customer for `axiom` is an irreducible trust boundary, especially
one connecting Heather's formal model to the outside world. The certifying
compiler should keep its internal claim clean:

```text
Compile<f> contains code plus a kernel-checked proof
formal_execution(code) = f
```

A later deployment layer may need a narrow external assumption such as:

```text
physical_execution(code) = formal_execution(code)
```

for a processor, emitter, loader, ABI, runtime, or FFI model. That bridge may
be an axiom when it must be stated inside Heather; otherwise it belongs in the
toolchain's reported trusted base. It should not be blurred into “trust the
compiler,” and it should not taint the `Compile` certificate before the
external bridge is actually used.

An opaque classical provider remains stuck. It may support propositional,
opaque proofs, but it cannot supply a reducing `Decide<P>` or executable
behavior. If a `Compile` certificate or deployment theorem uses an axiom,
ordinary provenance and project policy must be able to expose or reject it.

## Resolution and scope rules

There is one `infer`, with one observable priority:

1. an explicitly supplied argument;
2. an exact local binder or alias, innermost first;
3. existing scope/upcast and registered-instance derivations;
4. providers explicitly activated by a surrounding profile or `using` scope;
5. failure.

There is no `infer axiom`. Importing or merely naming an axiom never adds it
to step 4. Provider trials are checked at the requested goal and are
transactional: rejected or ambiguous candidates publish no dependency edges.
Diagnostics name the assumption/profile/using scope and the provider selected or
rejected.

Scopes are lexical and nest. An inner exact proof beats an outer broad
profile. A file-level assumption does not affect importers; they see ordinary
declaration signatures carrying the profile parameter. A concrete `using`
scope is likewise not re-exported as inference policy. Qualification and
module visibility continue to determine whether a named provider can be
activated, but visibility alone is never activation.

Closing over a capability or packaging it does not erase the outer
requirement. A callback built under `Classical` may have type `T -> U`, while
the declaration that creates it still has type `Classical -> T -> U`.
Existential or record packaging can hide the witness after it is supplied; it
cannot manufacture one. If an external boundary demands a genuinely closed
artifact, the choices are to retain the parameter, construct the capability,
or explicitly postulate it.

## Advisory lint

Because an `assuming` prefix is intentionally added to every enclosed
declaration, necessity is a lint rather than elaboration policy. The lint
should distinguish:

- a direct semantic use of the assumed binder or one of its providers;
- a call to another declaration that genuinely requires it;
- mere forwarding caused only by the callee's written generalized prefix.

Compute the least fixed point from direct-use seeds through declaration call
edges. A strongly connected component that only passes the parameter around
and has no direct-use seed does not justify itself. This avoids useless cycles
without making public types depend on proof-body inference. The diagnostic is
review/style advice and may suggest moving a declaration outside the block or
narrowing a broad profile to an exact premise.

## Discovery contract

Every declaration already exposes its implicit solver parameters; profiles
add derivation routes between those exact requirements and broader
capabilities. Tooling should therefore consume one structured **requirement
footprint**, not a special “classical theorem” bit:

- requirements already resolved in the cursor's context;
- unresolved exact propositions or typeclass capabilities;
- requirements obtainable by expanding an active or available profile;
- the concrete provider and axiom impact if one is selected.

Profile expansion for discovery must use the same resolution judgment and
precedence as elaboration. A theorem requiring `Stable<P>` should rank as
available when the current `ClassicalOn<A>` really derives it, and remain an
honest missing obligation otherwise. Search ranking is owned by
[[lemma-selection-and-search]], editor presentation by
[[lsp-from-the-meta-layer]], and agent-facing structured actions by
[[ai-facing-tooling]]. This issue owns only the semantic footprint and the
requirement/provider edges those consumers read.

## Acceptance

- Design one block-annotation model shared by theorem bodies, item groups or
  future namespaces, and the file's implicit top-level block.
- Implement `assuming` for an ordinary proposition and prove that every enclosed
  declaration receives the same leading implicit solver parameter, including
  a declaration whose body does not use it.
- Thread the generated parameter automatically through calls within and
  across generalized blocks; printed interfaces and diagnostics expose the
  real parameter.
- Define the profile interface and its ordinary kernel representation. Show a
  `Classical` profile providing polymorphic excluded middle to an exact
  `Or<P, Not(P)> := infer` premise.
- Demonstrate the library layering rule with a type- or proposition-indexed
  capability that has both a specialized constructive provider and a broad
  classical provider. The consumer names only the narrow capability.
- Include one justified classical convenience wrapper whose constructive
  source theorem has a materially different bound, witness, or API shape;
  reject a duplicate whose only difference is an inferable profile argument.
- Preserve exact-local-first behavior: the same theorem is called under the
  broad profile with a specialized constructive proof, and the specialized
  proof wins.
- Implement lexical `using` for a concrete ordinary profile value. Entering
  the scope alone creates no dependency, and nested scopes obey lexical
  precedence.
- Show one proved provider and one explicit axiom-backed provider used through
  the same `using` mechanism. Provenance is attached only to declarations
  that select the latter.
- Prove that a visible/imported but unactivated axiom is never considered by
  `infer`; there is no axiom-specific solver spelling or global logic mode.
- Diagnose missing and ambiguous providers with structured traces naming the
  exact local, profile, or `using` source considered.
- Keep classical evidence separate from `Decide<P>` and demonstrate that an
  opaque provider cannot satisfy the reducing decision contract.
- Add the advisory unused-assumption lint using direct-use seeds and SCC-aware
  transitive propagation, including a mutually recursive useless-forwarding
  control.
- Demonstrate the compiler boundary: an internal axiom-free `Compile`
  certificate and a separate deployment theorem whose narrow platform bridge
  is axiom-backed and reported by provenance.
- Decide the whole-file spelling and supply a local opt-out or narrowing form
  if real examples show that a file-level profile otherwise becomes
  irreversible.

## Non-goals

- Do not infer which declarations acquire an assumed parameter from their bodies.
- Do not search every proved global or every visible axiom for arbitrary
  evidence.
- Do not make importing a classical module activate classical reasoning.
- Do not make `assuming` a global elaborator mode or an implicit axiom.
- Do not register opaque excluded middle as `Decide<P>`.
- Do not require one monolithic `Classical` profile where narrower assumption
  interfaces state the actual dependency.
- Do not remove explicit `axiom`; keep it as the honest trust-boundary
  operation established by [[axiom-provenance]].

## Staged implementation

1. Land ordinary `assuming` item-group generalization and automatic parameter
   threading, with every enclosed declaration prefixed by construction.
2. Land lexical `using` for an ordinary concrete value and the corresponding
   resolution trace/provenance controls.
3. Design and land profiles using the smallest ordinary kernel
   representation that supports polymorphic providers; exercise exact local
   evidence against a broad `Classical` profile.
4. Add further parameterizable item kinds and the file-scale spelling over the
   same scope mechanism, then the unused-assumption fixed-point lint.
5. Exercise explicit axiom-backed closure only at the external/deployment
   boundary and keep the internal `Compile` path assumption-parametric.

## Implementation status

The first syntax slice is intentionally smaller than the semantic target:

- `assuming` parses a comma-separated mixture of named and anonymous general
  types and flattens nested item groups with outer requirements first;
- every enclosed `fn`, `theorem`, `axiom`, and `meta fn` receives ordinary
  leading `Solver::Infer` parameters marked with an `Assuming` origin;
- an enclosed `instance` receives the same telescope as leading inherited
  `requires`, so its members and assembled dictionary remain conditional and
  registry resolution backchains through the evidence rather than installing
  an ambient instance;
- anonymous `requires C<A>` also mints a hygienic solver parameter;
- anonymous generated names use one file-wide supply, remaining distinct when
  nested item groups are flattened onto one declaration;
- imports and item kinds whose parameterization route has not been audited are
  rejected explicitly inside the group rather than silently escaping it;
- the Rust parser, Tree-sitter grammar/highlighting, and end-to-end elaborator
  controls share the spelling.

Next on this issue is the remaining item-kind audit for `record`, `inductive`,
and `class`, whose assumptions must become honest parameters of their generated
types and constructors. Profiles, file scope, section-level type parameters,
`using`, and the unused-assumption lint remain later stages.

## What it assumes from elsewhere

- **[[axiom-provenance]]** owns explicit axioms and the committed dependency
  graph. Assumed here: an accepted axiom-backed provider records an ordinary
  global edge, while rejected trials and merely entering a scope do not.
- **[[traits]]** owns solver parameters and checked instance resolution.
  Assumed here: locals beat derivation, candidate trials are transactional,
  and the resolver can expose a structured trace.
- **[[scoped-instance-installation]]** owns named instance activation at
  module and block scope. Assumed here: `using` should share its lexical scope
  machinery where the provider is an instance, without mutating the registry.
- **[[decide-class]]** owns the reducing `Decide<P>` contract. Assumed here:
  opaque classical evidence cannot satisfy it.
- **[[modules]]** owns files as modules, imports, qualification, and
  visibility. Assumed here: file-level assumptions affect the file's implicit
  item block but are not imported as inference policy.
- **[[lint-review-only-mode]]** and **[[lint-roadmap]]** own advisory lint
  presentation. Assumed here: an unused-assumption analysis may be a review-only
  fixed-point check rather than a type-system rule.
- **[[compile-typeclass-design]]** owns `Compile`. Assumed here: its formal
  source-to-code equivalence can remain axiom-free; a physical-platform bridge
  is a separate consumer and trust boundary.
- **[[lemma-selection-and-search]]**, **[[lsp-from-the-meta-layer]]**, and
  **[[ai-facing-tooling]]** own search ranking, editor presentation, and
  agent-facing structured output respectively. Assumed here: all three consume
  the same requirement footprint and profile-expansion edges rather than a
  duplicated “classical” classification.

## Log

- 2026-08-24: Filed from the axiom-provenance follow-up discussion. Initial
  direction: assumptions are ordinary arguments, with local constructive
  evidence preferred over any broad classical route.
- 2026-08-24: Reconciled with [[decide-class]]: opaque excluded middle proves
  availability but cannot implement a reducing decision procedure.
- 2026-08-24: Replaced the proposed `infer axiom` fallback with a single
  `infer` plus explicit evidence scopes. Settled the four-way split:
  exact solver parameter; `assuming` item-group generalization; named profiles;
  concrete `using`.
- 2026-08-24: Settled that generalized block parameters are added to every
  declaration rather than inferred from body use. Unnecessary parameters are
  an SCC-aware advisory lint so proof refactors cannot silently change public
  types.
- 2026-08-24: Narrowed the purpose of `axiom`: classical developments may
  remain conditional indefinitely, while axioms are explicit trust leaves for
  deliberately closing a world, especially at formal-model/external-platform
  bridges. Internal `Compile` certificates should stay separate from that
  deployment trust boundary.
- 2026-08-25: Settled the library preference: exact proposition first,
  reusable indexed typeclass second, broad profile third. `Classical` is a
  common provider of narrow capabilities, not a consumer label. Classical
  wrappers remain valid where constructive precision bounds or witnesses
  produce a genuinely different API.
- 2026-08-25: Routed ergonomics through a shared requirement footprint.
  Search may expand profiles through the real resolver and rank by the
  requirements added at the cursor; the LSP may down-rank but not hide, while
  AI tooling receives the missing obligations, provider alternatives, and
  axiom impact as data.
- 2026-08-25: Implementation round opened on the group-only syntax. A single
  declaration continues to write an ordinary solver parameter or `requires`;
  `assuming h: P, C<A> { ... }` amortizes named and hygienic anonymous
  requirements over nested item groups. The first slice covers ordinary
  declarations and rejects unaudited item kinds by name.
- 2026-08-25: Extended group lowering to `instance`: inherited assumptions
  prepend its existing `requires` telescope and therefore flow through every
  synthesized member and the canonical dictionary. Positive and negative
  resolver controls demonstrate conditional backchaining. Also replaced the
  per-group anonymous-name index with a file-wide hygienic supply, preventing
  collisions when nested groups flatten.
- 2026-10-26: Refinement of "an opaque classical provider remains stuck": being stuck only
  costs computation when the axiom's type is relevant. An axiom whose type is
  squash-headed, such as `∥A + (A → Empty)∥`, is a stuck neutral that can only
  be eliminated into another squash. It should therefore leave closed
  canonicity at relevant types intact, and closed programs keep computing.
  This is a conjecture, proposed for checking in heather-coq. Felicissimo et
  al., LICS 2026 (`docs/papers/LIPIcs.LICS.2026.41.pdf`) prove the analogous result
  for irrelevant axioms that hold in a set model. For a classical profile, it
  argues for stating providers squashed whenever a squashed statement serves the
  consumer.
- 2026-11-05: gardener: cites a file it shares with [[squashed-termination-evidence]] (`docs/papers/LIPIcs.LICS.2026.41.pdf`).

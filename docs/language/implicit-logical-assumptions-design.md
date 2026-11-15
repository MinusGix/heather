# Implicit logical assumptions as ordinary evidence

Status: proposed 2026-08-24. Owner:
`issues/implicit-logical-assumptions.md`.

Companion records: `docs/kernel/axiom-provenance-design.md` defines explicit axioms
and records what an elaborated declaration actually used;
`docs/language/classes/traits-layer2-design.md` defines solver parameters and instance
resolution; `docs/language/classes/decide-class-design.md` fixes the computational meaning of
`Decide<P>`.

## 1. Direction

A theorem should express a logical assumption as an ordinary proof or class
parameter whenever it can. Omission may be ergonomic, but it must not erase
the parameter from the theorem's type.

In schematic syntax:

```hthr
theorem distinguish<P>(
    {hp: Or<P, Not(P)>},
    ...
): Result {
    ...
}
```

The braces here state the desired surface behavior: `hp` is an ordinary,
implicit kernel Pi binder whose value may be resolved at a use site. Heather's
currently landed general solver spelling is instead `hp: Or<P, Not(P)> :=
infer`; braced implicit parameters and solver parameters are deliberately
distinct today. Whether the final feature extends braces or uses the existing
solver spelling is a surface decision, not a semantic one.

This makes `distinguish` conditional rather than classical. A caller with a
constructive proof supplies it. A caller without one may allow a scoped axiom
to fill the same argument, and that caller—not `distinguish`—then acquires the
axiom dependency.

An excluded-middle *statement* consequently need not itself be an axiom. The
logical interface is the type `Or<P, Not(P)>`; an axiom is only one possible
provider of an inhabitant. This keeps the common use of an assumption in the
ordinary parameter/application language.

## 2. Resolution and provenance

For an omitted logical-evidence argument, the intended priority is:

1. an argument explicitly selected by the caller;
2. an exactly matching local hypothesis, innermost first;
3. a locally installed or constructively derived class value;
4. an eligible axiom in the lexical/import scope, as a fallback.

The first two rules already match the spirit of `infer`: named evidence in the
local context beats derivation. The fourth is the new policy. It must not mean
"search every theorem in the program"; unrestricted global proof search would
make resolution expensive, unstable, and difficult to explain. Explicit
axiom declarations are a bounded initial candidate set. Ordinary constructive
global providers should enter through the instance registry or an explicit
provider/installation mechanism.

Every proposed term is still checked at the requested type. Candidate trials
must remain transactional, as instance trials are now: rejected candidates do
not publish provenance. If resolution selects a global axiom, the ordinary
resolved global reference creates the dependency edge. No second propagation
mechanism is needed.

The resulting reports distinguish the theorem's interface from a particular
use:

```text
distinguish       requires Or<P, Not(P)>; no axiom dependency
general_case      omitted hp; resolver selected logic::classical_em
special_case      supplied a constructive hp; no axiom dependency
```

This is an operational statement. Provenance says which evidence the checked
term used, not whether excluded middle is mathematically necessary. Rewriting
a proof can remove the edge.

## 3. Narrow classes and broad classical capability

Some assumptions recur through many operations and make more sense as class
evidence than as a bare proposition at every call. The portable theorem should
still ask for the narrowest useful capability. Schematically:

```hthr
class Separates<P> {
    separate: Or<P, Not(P)>
}

theorem foo<P> requires s: Separates<P> (...) : Result {
    ...
}
```

A special carrier may provide `Separates<P>` constructively. A broad
`Classical` capability may provide it for arbitrary `P`. The dependency chain
then stays visible:

```text
consumer -> Separates<P> provider -> Classical provider -> classical axiom
```

The exact encoding of a broad capability—polymorphic record field, function
parameter, or a small family of principle classes—depends on the surface
available when this is implemented. The important rule is independent of that
encoding: broad classicality derives narrow logical evidence; consumers do
not need to advertise the broad capability when the narrow one states their
actual requirement.

## 4. `Decide<P>` is not classical evidence

Heather's landed class is:

```hthr
class Decide<P> { dec: Or<P, Not(P)> }
```

Its contract is stronger than mere inhabitation: `dec` reduces, so programs
may branch on it at kerneltime. An opaque classical axiom is neutral and does
not reduce. It may prove `Or<P, Not(P)>`, but it must not be registered as a
blanket `Decide<P>` instance. Doing so would make definitions typecheck while
silently destroying the computation promised by `Decide`.

Therefore the layers remain separate:

- a bare implicit proof or a logical-evidence class says a proposition is
  available, possibly from an opaque axiom;
- `Decide<P>` says a reducing decision procedure is available;
- `Compile` additionally owns executable representation and cost evidence.

A theorem that only reasons propositionally may accept classical evidence. A
function whose result must compute should require `Decide<P>` and cannot be
made computational merely by assuming classical logic.

## 5. What “assume classical” should mean

“Assume classical” should be parameter introduction, not a global elaborator
mode. A future lexical form could be equivalent to placing a `Classical`
solver parameter on declarations in a section:

```hthr
assuming classical: Classical {
    theorem foo(...) : Result {
        // narrow evidence may be derived from `classical`
    }
}
```

The declaration produced by this block remains conditional on `Classical`.
It has no axiom provenance merely because the section was written. At a use
site, the parameter may be supplied constructively or resolved to a scoped
global axiom; only the latter choice creates an axiom edge.

This form should also make the relevant instance bundle available lexically,
without installing a blanket classical instance everywhere. It composes with
the separately tracked scoped-instance direction:

- `assuming classical: Classical` introduces an ordinary local value;
- instances requiring that value can derive narrower evidence;
- `use instance ...` controls which named derivations participate in the
  lexical scope;
- resolving the outer capability from an axiom records the trust dependency.

The desugaring policy remains open. Adding the parameter to every declaration
is simple and explicit but may leave unused parameters. Adding it only to
declarations whose bodies resolve through it produces smaller interfaces but
makes signatures depend on elaboration. The conservative starting point is an
explicit parameter or `requires` binder; section sugar should follow only
after that behavior is understood.

## 6. Guardrails and diagnostics

- Local and specialized evidence must beat a broad axiom-backed fallback.
- Importing a classical module must not silently install a blanket
  computational `Decide` instance.
- Ambiguous axiom providers should be diagnosed with the same checked
  candidate trace as other resolution ambiguity, including module-qualified
  names.
- Diagnostics for an omitted argument should say whether search considered
  locals, registered instances, and scoped axioms.
- `heather axioms` should show the provider chain chosen at each committed
  declaration; it need not guess whether a narrower assumption would suffice.
- Cache identity follows the selected resolved globals, so changing an
  axiom-backed discharge to a constructive one moves the dependent closure
  naturally.

## 7. Staged implementation

1. Let a general solver parameter opt into scoped-axiom fallback, preserving
   the current local-first rule and transactional candidate accounting.
2. Demonstrate a theorem whose proposition-specific evidence is supplied
   classically in one caller and constructively in another; assert different
   provenance reports.
3. Demonstrate the class route with a narrow logical-evidence class and a
   broad capability, without involving `Decide<P>`.
4. Design the lexical `assuming`/instance-installation sugar from those
   examples rather than making classicality an elaborator mode.

This staging makes the first useful feature an extension of ordinary
arguments. Bundling and scope sugar remain library and ergonomics layers over
the same kernel terms.

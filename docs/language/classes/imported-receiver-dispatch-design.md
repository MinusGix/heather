# Imported receiver dispatch

`issues/result-map-receiver-dispatch.md`. Customer:
`docs/showcase/calc_parser.hthr`.

## Failure and policy

List, Option and Result export ordinary functions named `map`. Under combined
imports the bare name is ambiguous. `shadowed` asks for a successfully resolved
global, so ambiguity looked like absence to the builtin vector-map branch.
A Result receiver therefore reached a vector error; a vector receiver could
silently reach the builtin even in a bare `map(v, f)` call.

Dot syntax now has a narrow disambiguation rule for **ambiguous imported
names**. Fields, local bindings, selected imports, unique ambient declarations,
and nominal type-owned members keep their existing routes. This does not
turn every unique method name into an overload search.

For an ambiguous import set:

1. Infer the receiver. Preserve its inference error if this fails.
2. Read its outer carrier: the canonical declaration key for an inductive or
   record, `Nat`, or the primitive vector former.
3. Read each candidate's receiver domain from its committed kernel signature,
   respecting its `self` position (or the first explicit parameter). Enter
   earlier parameters as neutral binders in a temporary context. Global
   references are rescoped from the binding's prefix to the current world.
4. Discard only candidates with a known, different outer carrier.
5. Select a sole remaining known candidate only when no unknown candidate
   remains. Multiple candidates with the same carrier stay ambiguous.
6. If all declared candidates are known to differ and the receiver is a
   vector, `map` can use the existing vector intrinsic. Class-backed dispatch
   still gets its normal opportunity to report competing readings first.

An unknown domain, including generic `self x: A`, is not evidence that a
candidate is inapplicable. Type arguments, callback types, successful callback
elaboration, and import order do not break ties. For example, two functions
on `Result<...>` remain ambiguous even if a later argument could distinguish
their instantiations. Explicit qualification remains the resolution escape.
Canonical declaration keys distinguish identically spelled types declared
in different modules. No surface-name guessing or new serialized registry
is involved.

Bare `map(...)` retains name-based module resolution: ambiguous declarations
now report ambiguity instead of falling through to the intrinsic. The new
receiver-selected intrinsic result has an explicit dot-resolution case, so
it does not pass back through ambiguous bare-name lookup. Its checking path
records expected-type mismatches just as the ordinary inference fallback does.

## Scope and cost

Only ambiguous names cause signature inspection and extra receiver inference.
There is no speculative callback execution, unification-world sharing, or
change to the kernel. The library APIs retain their names and implementation.
Alias or dependent domains whose carrier cannot be established conservatively
remain ambiguous; this is a dispatch limit, not general instance search.

This dispatch round changed the calculator to
`.map(λ (n: Nat) => Some<List<Nat>>([n]))`. The subsequent callback round
removed that container annotation; see `docs/elaborator/callback-expected-types-design.md`.

## Validation

`crates/elab/tests/imported_receiver_dispatch.rs` covers polymorphic neutral
receivers, closed equations, import order, unrelated carriers, genuine and
unknown-carrier ambiguities, local declarations and aliases, selected imports,
callable record fields, explicit qualification, non-first `self`, and nominal
identity across modules. Controls reject wrong callbacks, wrong vector result
types, false equations, invalid builtin arguments, and ambiguous bare calls.

The calculator acceptance also exercises actual List, Result, Option and
primitive-vector map calls together under the library imports. Existing
record, nominal-member, receiver-position and class-dispatch suites remain
part of validation.

Full `scripts/test`: **2647 passed, 0 failed, 5 ignored**.
The isolated benchmark gate reports six Nat timing flags; the unchanged
kernel/baseline investigation is recorded in
`issues/kernel-benchmark-nat-baseline-drift.md`. The baseline was not rewritten.

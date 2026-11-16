# Typed local contexts for decrease obligations

Owner: `issues/typed-termination-obligations.md`.

## Boundary

The well-founded lowering still emits ordinary Heather declarations. Its
induction hypothesis, measure scaling, and declaration-order rank rules are
unchanged. The change supplies type information to the lowering's local
scope rather than replacing the recursion representation.

The old scope knew written parameter/let types and plain constructor fields.
It could not type an inferred let or a field-expression scrutinee. Lifting
also selected only names occurring directly in the goal or its discharge,
so a selected hypothesis could lose variables needed to state its type.

## Type recovery

An isolated elaborator query reconstructs a local telescope from the type
parameters and known local types. Group signatures are neutral local
functions in that query; they are never committed definitions or assumptions.
The ordinary elaborator infers a let initializer or scrutinee in that context.
Recovered types are spelled as source, re-elaborated, and compared with the
inferred type before the lowering uses them as telescope annotations. If a
structural type has no complete spelling, a recursive signature or stored
function declaration supplies a candidate result type, instantiated at the
call's arguments. For ordinary polymorphic functions those arguments come
from the elaborated application, including inferred type arguments. This
candidate must pass the same comparison; stored source never overrides the
inferred type.

The source spelling retains value arguments of records, using the existing
checked instance matcher and generated type-code application spines. An
incomplete or ambiguous spelling is declined, rather than used as a type.
The query's goals, warnings, and other speculative state are discarded.

Postfix `?` has already become a Result call and a private continuation by
this stage. Its continuation parameter gets the preceding input's success
payload type before the lowering walks the continuation. This lets ordinary
inference type the source binding inside it. The written source needs no
annotation on the successful parse result.

A computed match scrutinee is bound once to a fresh internal local with its
recovered type. The match then uses that local, preserving the dependent
match's computation behavior and providing a named equation in its scope.
Bare nullary constructors in nested patterns are recognized from the field's
type and do not become spurious local variables.

## Dependency closure and proof order

The lifting pass closes selected locals over their types in reverse binding
order. Match equation binders carry their equation types, so a hypothesis
whose type mentions an equation also brings that equation and its own
parameters. References in annotations and explicit type arguments count.
A shadowed dependency that cannot be spelled unambiguously declines lifting.

A recursive call is rewritten and its obligation generated before its result
is added to the local scope. The result cannot discharge its own precondition.
A prior call's result can be used by a later call, but the emitted body still
has to construct that prior result through the induction hypothesis and its
own checked decrease proof. The type queries do not bypass either proof.
Failed families roll back their committed declarations through the existing
session transaction mechanism. All emitted definitions and proof terms still
pass the kernel gate.

## Client and limits

The calculator infers `left`, `right`, and `inner`, and matches `left.rest`
and `inner.rest` directly. Automatic selection subsequently removes its
explicit decrease discharges; see `docs/language/recursion/termination-local-evidence-design.md`.

Type recovery is conservative. Unknown local types, unsupported source
spellings, and patterns whose field types cannot be recovered may still
prevent lifting. This does not introduce general inference for arbitrary
callbacks or change the existing unfolding-companion shape restrictions.

## Validation

`crates/elab/tests/typed_termination_contexts.rs` exercises a mutual group
with inferred value-indexed records over an open element type, inferred local
decrease evidence, field-expression matches, and literal/neutral clients.
The helper's type parameter has a different name from the group's, so type
argument recovery cannot depend on matching names. A second case lifts a
hypothesis whose type mentions a match equation. Negative controls cover
nondecreasing cycles, false evidence, ill-typed arguments, circular use of a
call's own result, and reuse of the same elaborator after a failed group.

The calculator acceptance retains its AST and pipeline equations and false
result controls. The existing single-function, mutual rank, and unfolding
suites remain acceptance gates.

Full `scripts/test`: **2655 passed, 0 failed, 5 ignored**.
The isolated benchmark gate reports four Nat timing flags, with no slope
failures. Observations remain with `issues/kernel-benchmark-nat-baseline-drift.md`;
the baseline was not rewritten.

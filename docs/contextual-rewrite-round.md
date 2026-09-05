# One contextual rewrite

This round connects a local relation proof to the surrounding expressions in a
theorem. The [input](showcase/contextual_rewrite_input.hthr) is:

```heather
theorem rewrite_receive<A>(known, xs, ys: List<A>, h: SameMembers<A>(xs, ys)):
    SameMembers<A>(known ++ (xs ++ xs), known ++ (ys ++ ys))
{ ?rewrite }
```

The request selects this theorem and `h`, together with append's existing
compatibility certificate and membership reflexivity for `known`. The entry
point reads both relations and their endpoints from the declaration. The user
does not write the context function or the compatibility proof.

It recovers, with a fresh binder, the context:

```heather
λ (incoming: List<A>) => known ++ (incoming ++ incoming)
```

It asks the existing context-certificate planner to prove preservation for this
function, then applies the resulting certificate to `xs`, `ys`, and `h`.
The output is the original theorem with an ordinary proof body replacing the
hole. It is checked before being returned and can be checked independently.
The [saved generated theorem](showcase/contextual_rewrite_generated.hthr) is the
exact successful driver output.

`?rewrite` is an ordinary goal hole, not a newly implemented tactic keyword.
The temporary source driver performs the replacement. Native proof-position
integration and boxed-code/meta-layer implementation remain future work.

## Try the driver

```console
furnace run -- scripts/relational-context-demo rewrite
furnace run -- scripts/relational-context-demo rewrite-missing-observer
furnace run -- scripts/relational-context-demo rewrite-supplied-observer
furnace run -- scripts/relational-context-demo rewrite-mismatch
furnace run -- scripts/relational-context-demo rewrite-length
```

Success prints only checked source on stdout. Missing evidence exits 1 and
prints well-formed goal declarations on stderr. A mismatch or invalid request
exits 2. A blocked or rejected rewrite produces no candidate source.

The observer modes wrap both endpoints in `observe`. The generator leaves
`PreservesRelation(SameMembers<A>, SameMembers<A>, observe<A>)` until its
certificate is supplied. It does not unfold the observer's implementation.
The length mode leaves the corresponding Nat-identity preservation obligation;
it does not mistake membership equivalence for representative identity.

The mismatch mode changes a fixed prefix as well as `xs` to `ys`. Its error
identifies the first argument where the supplied proof cannot explain the
change. That rejects this structural derivation; it does not prove the goal
false.

## Which occurrences change?

Recovery compares the two endpoint trees in parallel:

1. Identical subexpressions remain fixed.
2. A differing pair exactly matching the supplied proof's endpoints becomes
   the context variable.
3. Otherwise, matching application heads are traversed argument by argument.
4. Any unexplained difference is a mismatch.

For `xs ++ xs` to `ys ++ xs`, only the first occurrence changes. The second
requires its own fixed-value evidence from the explicit rule table. This is
not global replacement of every textual `xs`.

An identical pair of goal endpoints produces a constant context with zero
changed occurrences. Even then, the generator must construct its compatibility
certificate; syntactic sameness does not invent relational evidence. Equal
proof endpoints similarly do not justify any syntactically different goal
endpoints. No symmetry, reduction, or function extensionality is guessed.

Fresh names are chosen against the source and rule text. This prevents a
recovered binder or certificate variable from capturing a user parameter.
No traversal under lambda or dependent binders is supported in this round.

## API and checking boundary

`heather_elab::relational_context::rewrite` accepts a `RewriteRequest` naming
the theorem, proof parameter, operation rules and fixed-value evidence. Its
`RewriteResult` exposes the recovered typed context, occurrence count, and the
same checked/blocked `Outcome` used by declaration-level generation.

The original assumptions and target type are checked through a Type-valued
probe in a private elaborator clone. This does not declare an axiom for the
unfinished theorem. Missing goals are likewise checked for well-formedness
in the original binder context, with spans into the original input source.
On success, the entire rewritten module goes through ordinary checking.
The caller's elaborator is never modified. Required helper-module imports are
added when absent, without duplicating existing imports. Existing selective
imports remain selective and must expose the referenced helpers.

Both entry points use the existing `Walker` and the same library proof rules.
There is no second collection of congruence axioms or special rule for append.
The final check rejects false supplied certificates and incorrect operation
mappings, even after structural recovery has succeeded.

## Current limits

- The selected theorem has explicit value parameters, Type<0> type parameters,
  and a single hole body. Local proof steps are not yet an input to this API.
- The selected proof parameter is written as a binary relation application.
  Its endpoints are named value parameters with the same written carrier type.
  Compound endpoints and proof expressions require later elaborator integration.
- Goal endpoints are binder-free variable/numeral/unary-or-binary-call trees.
  Each side has a 256-node / depth-32 bound. Matching is structural and
  conservative; function bodies are not unfolded.
- Relation spellings must match the explicit rule table, including type
  arguments. The examples write `SameMembers<A>` deliberately. Native `=`
  statements are not decoded here; `RelId<T>(left, right)` is the current
  explicit identity spelling for this source-level entry point.
- Missing certificates are resumed by rerunning with additional evidence.
  A general occurrence-selection interface, relation search, dependent contexts,
  relational `calc`, and the meta-layer port are not part of this slice.

## Validation

All five driver modes produce their expected outcomes and exit codes. The saved
generated theorem passes an independent `heather check` through Furnace (with
existing unused-payload warnings in imported standard-library modules).

The required plain `furnace run -- scripts/test` passed: **2,336 passed,
0 failed, 5 ignored**, including all 21 setoid/generator/rewrite tests. The
completed run took 222 seconds with warm caches. An earlier attempt was
interrupted with exit 143 before completion and was not counted as validation.

# A bounded context-proof generator

The first generator turns an ordinary source function and an explicit table of
compatibility certificates into a checked Heather definition. The runnable
[input file](showcase/relational_generator_input.hthr) includes:

```heather
fn receive<A>(known, incoming: List<A>) -> List<A> {
    known ++ (incoming ++ incoming)
}
```

The request selects `incoming`, `SameMembers<A>` as both input and output
relation, append's existing compatibility certificate, and membership
reflexivity for `known`. The result proves preservation for `receive` itself.
The [saved generated definition](showcase/relational_generator_generated.hthr)
is ordinary Heather source, independently checkable without invoking the
generator again.

## Try it

From the repository root:

```console
furnace run -- scripts/relational-context-demo success
furnace run -- scripts/relational-context-demo missing-observer
furnace run -- scripts/relational-context-demo supplied-observer
furnace run -- scripts/relational-context-demo length
```

The driver prints complete checked source on stdout only on success. Missing
evidence goes to stderr and exits 1; malformed requests or failed checking
exit 2. It is a temporary explicit driver, not proposed language syntax.
The Rust request is visible in `crates/cli/examples/relational_context.rs`.

The missing-observer run stops at:

```heather
PreservesRelation(SameMembers<A>, SameMembers<A>, observe<A>)
```

The supplied-observer run gives that same operation its certificate and succeeds.
The generator never inspects `observe`'s implementation, even though this tiny
demo implementation is an ordinary transparent identity function. This models
an abstraction boundary, without an axiom standing in for the operation.

The length run instead leaves:

```heather
PreservesRelation(SameMembers<A>, RelId<Nat>, list_len<A>)
```

That is an unresolved obligation, not a generator-produced counterexample.
[The preceding checked showcase](showcase/mergeable.hthr) independently refutes
this claim with `[0, 0]` and `[0]`.

## What the entry point guarantees

`heather_elab::relational_context::derive` takes a dependency environment,
a module name, ordinary source, and a `Request`. It returns either a checked
augmented source module or structured obligations containing a source span,
reason, goal, and Type-valued declaration displaying the goal's binder context.
Those declarations are checked for well-formedness; they do not assert their
inhabitance.

Input checking, obligation checking, and final generated-proof checking use
private elaborator clones. The caller's session gains no definitions on either
success or failure. A blocked result contains no candidate certificate, inserts
no holes or assumptions, and registers no instance. Resumption is deterministic
rerunning with the missing evidence supplied, not a suspended elaborator state.

A rule table cannot assert preservation by itself. A mistaken operation mapping
or a false supplied certificate must survive the ordinary final kernel check.
The tests deliberately mutate a rule to verify rejection at that boundary.

## Deliberately small fragment

- Plain `fn`s with explicit value parameters and unconstrained Type<0> type
  parameters, with an expression body and no local statements.
- One selected varying parameter; the other parameters remain explicit binders
  of the generated certificate.
- Variables, fixed parameter names/numerals, and unary/binary positional calls
  with explicitly registered signatures. Infix calls such as `++` can be mapped
  to their named operation; the final check verifies that mapping.
- Explicit input, intermediate and output relations. Matching is textual and
  conservative; definitional equality is not used to choose between rules.
- At most 256 visited expression nodes and depth 32. Ambiguous applicable rules
  are errors. No search, unfolding, recursion, dependent transport, implicit
  coercion, or instance discovery.

The proof tree uses `respectful_id`, `respectful_const`,
`preserves_relation_compose`, and `preserves_relation_binary`. Fixed terms need
supplied self-relation evidence for the constant rule. These sufficient rules
are not a complete preservation decision procedure.

Unsupported expressions can leave a whole-context preservation obligation.
Unsupported declaration shapes or goals that cannot be stated in the retained
binder context produce an explicit error. No dependent binder is silently
rewritten or generalized.

## Prototype boundary and follow-up

This is a **source-AST prototype in Rust**, with the existing Heather emission
IR and an ordinary checking boundary. It is not the boxed-code generator
specified by the broader auto-lifting issue, and does not change the existing
in-language compiler transcriber. Its small traversal makes the first client
contract and failures executable before adding a reflection entry point or a
meta-layer slot. Moving analysis/proof planning into Heather remains required
for the intended user-extensible generator.

The next integration should preserve this contract while replacing the source
walk with reflected code. Relational `calc` can then consume the same checked
certificate machinery. Richer relation selection, proof search, caching and
resumable interactive obligations remain separate work.

## Validation

Focused Furnace run: **13 passed, 0 failed**. Final plain
`furnace run -- scripts/test`: **2,328 passed, 0 failed, 5 ignored**.
All four standalone driver modes returned the expected exit codes; blocked
modes emitted no source on stdout. The saved generated source also passed
a separate ordinary `heather check` through Furnace (with existing unused-payload
warnings in its standard-library imports). Formatting and tracker checks pass.

# Explicit axioms and provenance

Status: landed 2026-08-24. Owner: `issues/axiom-provenance.md`.

Companion future direction:
`docs/language/implicit-logical-assumptions-design.md` treats assumptions as ordinary
implicit proof or class parameters, with scoped axioms as one possible
provider. This document records the trust edge once such a provider is
selected.

## Surface and trust boundary

An assumption is written only as a bodiless declaration:

```hthr
axiom funext<A>(f, g: A -> A): f = g;
```

The semicolon is part of the form. `axiom … { proof }`, `theorem …;`, and the
alias `postulate` are rejected, so an omitted proof cannot silently change a
theorem into an assumption. Parameters use the ordinary declaration telescope.
The elaborator checks the statement as a kernel type, then commits the same
opaque `GlobalBinding::Tm` the kernel already uses for assumptions. No proof is
invented and no term-check gate runs.

The kernel deliberately does not distinguish an opaque proved theorem from an
assumption: both are legal global hypotheses in the calculus. The distinction
is a source/trust fact and lives in elaborator metadata.

## The committed graph

`PendingDecl` carries two additional facts to the sole ordinary-declaration
commit point:

- whether the declaration is an explicit user axiom;
- the resolved, module-qualified identities of globals referenced by its
  checked proof or body.

References in the public statement alone are not proof dependencies. The set
is collected only while the body is elaborated, after the statement has been
lowered. Generated declarations and instance artifacts use the same ordinary
declaration path, so their intermediate nodes remain visible in provenance
paths. A session checkpoint includes the graph; a failed generated bundle
therefore publishes none of its assumptions or edges.

At commit, direct edges are sorted and deduplicated. For every reachable axiom
the registry retains the shortest path from the new declaration, breaking
equal-length ties lexicographically. This makes reports deterministic without
depending on hash-table iteration or traversal order. Keys are resolved
identities such as `logic::classical`, never basenames.

## Inspection and policy

```text
heather axioms <target> [-L <dir>]... [--json] <file-or-dir>...
heather check --deny-axioms <file-or-dir>...
```

The text report prints each assumption's kind and one path. JSON returns a
stable slice with the target, whether it is itself an axiom, its direct edges,
and `{name, kind, path}` for each reachable assumption. The public API exposes
the same `AxiomReport` data. `--deny-axioms` is the first project policy: it
rejects every proved or computing declaration in the selected check closure
whose transitive set is nonempty; merely declaring an unused axiom is not a
violation.

The kind vocabulary distinguishes `user` and `primitive`. This round has no
primitive assumptions to register—the fixed kernel formers are rules, not
axioms—but the output schema does not need to change when one is introduced.

## Cache identity

An axiom and an opaque theorem with the same statement have identical kernel
bindings, but different trust interfaces. The cache receives an assumption
notification after the axiom statement passes `check_type` and hashes it under
a separate interface domain. Consequently replacing `axiom a: P;` with
`theorem a: P { proof }` moves every dependent closure key even though `P` did
not change.

## Deliberate boundaries

- There is no package manifest yet, so axiom permission is selected by the
  check invocation rather than stored package policy.
- Heather has no generated API-documentation command. The structured report
  and public metadata are the source a future documentation renderer consumes;
  no second provenance table should be introduced there.
- Ordinary opaque theorems appear as graph nodes but never as assumptions.
  Their proofs were checked before opacity and their edges were captured at
  that point.

# Describe the representation once

The [lift showcase](showcase/lift_positive.hthr) now gives its representation
a name and reuses it for both construction and the projection theorem:

```heather
fn Positive(n: Nat) → Type { 0 < n }

fn positive_repr() → SubtypeRepr<Nat, PositiveNat>(Positive) {
    SubtypeRepr(
        project := λ x => x.value,
        pack := λ n p => PositiveNat(n, p),
        holds := λ x => x.valid,
        project_pack := λ n p => refl)
}
```

`SubtypeRepr` in [`lib/subtype.hthr`](../lib/subtype.hthr) packages how to read
a value, construct one with evidence, recover its invariant, and prove that
construction preserves the supplied value. Its predicate is an explicit
index; the representation never chooses an invariant merely from a carrier.
The evidence in this customer remains relevant.

The operation and theorem now read:

```heather
fn lifted_add(x, y: PositiveNat) → PositiveNat {
    lift_binary(positive_repr(), add, positive_add_closed, x, y)
}

theorem lifted_add_value(x, y: PositiveNat):
    lifted_add(x, y).value = x.value + y.value
{
    lift_binary_value(positive_repr(), add, positive_add_closed, x, y)
}
```

These ordinary library functions call the existing Heather templates. Their
surface signatures retain implicit-argument information, so callers do not
repeat the ambient type, subtype, or predicate. The raw `emit_code` interface
remains available for template authors. No new compiler rule was needed for
the packaged interface.

Closure is still an explicit argument. Replacing it with `?closure` leaves
an ordinary goal, repaired with `on ?closure := positive_add_closed;`. A
constructor that changes the value fails the representation's `project_pack`
obligation. The same representation is reused by an Omega-backed lift in the
[arithmetic showcase](showcase/positive_omega.hthr).

## Omega already handles this arithmetic

This checked theorem has exactly the arithmetic needed for addition:

```heather
theorem projected_sum_positive(x, y: PositiveNat, positive: 0 < x.value):
    0 < x.value + y.value
{ omega }
```

The caller supplies `x.valid` to that helper. Its proof then serves as the
closure argument of `lift_binary`, and the projection theorem is generated
in exactly the same way as before. No positivity-specific tactic is needed
for this linear example.

The probe also found two practical limitations. A local alias
`let positive = x.valid; omega` does not currently add that proof to Omega's
collected hypotheses. And its generated certificate needs `logic`, `int`,
and `list` imported alongside `nat` and `omega`. The showcase uses those
imports explicitly and passes the evidence as a helper parameter.

A sensible next automation step is making explicitly supplied local facts
available to the existing solver. A broader positivity tactic could later
compose preservation lemmas for operations outside Omega's affine fragment,
such as products with two variable operands. It should reuse Omega for
linear consequences rather than duplicate its arithmetic engine.

## Remaining inference detail

The named predicate `Positive` is significant today. An anonymous
`λ n => 0 < n` index checks as a representation type, but the concise call
then fails to infer `lift_binary`'s implicit `P`. Naming the predicate is the
checked workaround; we have not changed unification in this round.

The findings are tracked in [local proof aliases](../issues/omega-local-proof-aliases.md),
[certificate imports](../issues/omega-certificate-imports.md), and
[anonymous predicate inference](../issues/lambda-predicate-index-inference.md).

Validation: 46 focused tests passed; both showcases passed through the ordinary
CLI; final plain `furnace run -- scripts/test` passed with 2,375 tests passed,
none failed, and 5 ignored.

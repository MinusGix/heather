# When the evidence computes

The [witness showcase](showcase/witness_subtype.hthr) stores a natural number
alongside a chosen upper bound and a proof that the bound is large enough.
Two values can represent the same number while carrying different bounds.
This is ordinary relevant evidence: a function can read it and compute with it.

```heather
fn HasBound(n: Nat) → Type { Exists<Nat>(λ bound => n <= bound) }
record WitnessedNat { value: Nat, evidence: HasBound(value) }
fn SameNumber(x, y: WitnessedNat) → Type { x.value = y.value }
fn chosen_bound(x: WitnessedNat) → Nat { x.evidence.witness }
```

The same `SubtypeRepr` and `lift_binary` interface used for positive naturals
works here. To lift addition, `sum_has_bound` chooses the sum of the input
bounds and proves that it bounds the sum. It is a transparent function returning
evidence: an opaque theorem would hide the chosen witness from computation. The resulting operation has both
an ordinary value theorem and a computation theorem for its retained witness:

```heather
theorem witnessed_add_bound(x, y: WitnessedNat):
    chosen_bound(witnessed_add(x, y)) = chosen_bound(x) + chosen_bound(y)
{ refl }
```

Addition respects `SameNumber` and is associative under that relation.
Its closure argument can inspect evidence even though its abstract value
laws ignore evidence. There is no need to squash the witness or identify
all proofs to establish those laws.

## What cannot transfer automatically

The showcase constructs zero with bound zero and zero with bound one.
They satisfy `SameNumber`, but their chosen bounds differ. The theorem
`bound_reader_cannot_ignore_evidence` turns any claimed compatibility proof
for `chosen_bound` under `SameNumber` into `False`. This is a supplied,
checked counterexample, not a counterexample finder or a diagnostic guessing
that two representations must differ.

A dependent result makes the distinction visible in its type:

```heather
fn bound_index(x: WitnessedNat) → Fin(Succ(chosen_bound(x))) { FZ }
```

Knowing only `SameNumber(x, y)` does not identify these two `Fin` indices.
The regression refuses to reuse an arbitrary index from the first fiber in
the second, while accepting construction of a fresh zero index there. One
could still design a map between the fibers, or choose a
relation that also relates the bounds. Such a map needs its own specification;
value equality alone does not supply equality transport.

For future lifting automation, the useful question is therefore concrete:
which observations and result types must the requested relation preserve?
The present round checks a small customer of that question. General dependent
relational transport and coherence remain open.

## The small Omega improvement

The [positive arithmetic showcase](showcase/positive_omega.hthr) now writes:

```heather
theorem record_sum_positive(x, y: PositiveNat): 0 < x.value + y.value {
    let positive = x.valid;
    omega
}
```

Omega collects explicitly named aliases using ordinary name resolution,
including binder shadowing and aliases used beneath later binders. It does
not search record fields for an invariant. The generated certificate names
its own library dependencies, so clients need `nat` and `omega` but no extra
`logic`, `int`, or `list` imports solely for reconstruction. That visibility
is confined to certificate generation and checking; missing `omega` produces
an import suggestion. Certificates still pass ordinary elaboration and the
kernel gate.

## Validation

The focused setoid/subtype target passed all 48 tests. Final plain
`furnace run -- scripts/test`: 2,377 passed, 0 failed, 5 ignored.
The suite includes alias dependency/shadowing, insufficient evidence,
generated-name collisions, missing-library diagnostics, import isolation,
witness computation, and invalid dependent reuse controls. The certificate
source-size snapshot was updated for qualified names; its structural hoisting
checks remain intact.

Both showcases also pass ordinary CLI checking on Furnace with explicit
`-L lib/std -L lib -L docs/showcase` search paths. Existing library lint
warnings remain. Issue lint passes for all 456 issues.
